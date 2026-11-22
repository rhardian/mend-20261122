import { mkdirSync, readFileSync, rmSync, statSync, writeFileSync, writeSync } from 'node:fs';
import { dirname } from 'node:path';

type PatchFormat = 'auto' | 'unified' | 'search-replace' | 'v4a' | 'json';
type ConcreteFormat = 'unified' | 'search-replace' | 'v4a' | 'json';
type FailureCode = 'no-match' | 'ambiguous' | 'missing' | 'exists' | 'unsafe';
type MatchTier = 0 | 1 | 2;

const VALID_FORMATS = new Set<string>(['auto', 'unified', 'search-replace', 'v4a', 'json']);

class Exit2Error {
  readonly message: string;
  constructor(message: string) {
    this.message = message;
  }
}

class EditFailure {
  readonly code: FailureCode;
  readonly path: string;
  constructor(code: FailureCode, path: string) {
    this.code = code;
    this.path = path;
  }
}

interface TextDocument {
  lines: string[];
  lineBreak: string;
  endsWithBreak: boolean;
}

interface BodyItem {
  kind: 'ctx' | 'del' | 'add';
  text: string;
  noEol: boolean;
}

interface UnifiedHunk {
  oldStart: number;
  items: BodyItem[];
}

interface UnifiedSection {
  gitOld: string | null;
  gitNew: string | null;
  minusPath: string | null;
  plusPath: string | null;
  renameFrom: string | null;
  renameTo: string | null;
  isNewFile: boolean;
  isDeletedFile: boolean;
  hunks: UnifiedHunk[];
}

interface V4aChunk {
  anchor: string | null;
  items: BodyItem[];
  eof: boolean;
}

type EditFn = (tree: VirtualTree) => void;

function isBlank(line: string): boolean {
  return line.trim() === '';
}

function isSafePath(p: string): boolean {
  if (p === '' || p.startsWith('/') || p.includes('\\')) return false;
  const segments = p.split('/');
  for (const seg of segments) {
    if (seg === '' || seg === '.' || seg === '..') return false;
  }
  return true;
}

function splitPatchLines(text: string): string[] {
  if (text === '') return [];
  const raw = text.split('\n');
  if (text.endsWith('\n')) raw.pop();
  return raw.map((line) => (line.endsWith('\r') ? line.slice(0, -1) : line));
}

function splitDocument(text: string): TextDocument {
  const firstLf = text.indexOf('\n');
  const lineBreak = firstLf > 0 && text[firstLf - 1] === '\r' ? '\r\n' : '\n';
  if (text === '') return { lines: [], lineBreak, endsWithBreak: false };
  const endsWithBreak = text.endsWith(lineBreak);
  const lines = text.split(lineBreak);
  if (endsWithBreak) lines.pop();
  return { lines, lineBreak, endsWithBreak };
}

function joinDocument(doc: TextDocument): string {
  if (doc.lines.length === 0) return '';
  return doc.lines.join(doc.lineBreak) + (doc.endsWithBreak ? doc.lineBreak : '');
}

function utf8ByteCompare(a: string, b: string): number {
  return Buffer.compare(Buffer.from(a, 'utf8'), Buffer.from(b, 'utf8'));
}

class VirtualTree {
  private readonly diskCache = new Map<string, string | null>();
  readonly overlay = new Map<string, string | null>();
  readonly movedFrom = new Map<string, string>();

  original(p: string): string | null {
    if (!this.diskCache.has(p)) {
      let content: string | null = null;
      try {
        if (statSync(p).isFile()) {
          content = readFileSync(p, 'utf8');
        }
      } catch {
        content = null;
      }
      this.diskCache.set(p, content);
    }
    return this.diskCache.get(p)!;
  }

  get(p: string): string | null {
    return this.overlay.has(p) ? this.overlay.get(p)! : this.original(p);
  }

  set(p: string, content: string): void {
    this.overlay.set(p, content);
  }

  remove(p: string): void {
    this.overlay.set(p, null);
    this.movedFrom.delete(p);
  }

  recordMove(fromPath: string, toPath: string): void {
    this.movedFrom.set(toPath, fromPath);
  }
}

function detectFormat(lines: string[]): ConcreteFormat | null {
  const firstNonBlank = lines.findIndex((line) => !isBlank(line));
  if (firstNonBlank < 0) return null;
  if (lines[firstNonBlank]!.trim() === '*** Begin Patch') return 'v4a';
  const leadChar = lines[firstNonBlank]!.trimStart()[0];
  if (leadChar === '[' || leadChar === '{') return 'json';
  if (lines.some((line) => line.trimEnd() === '<<<<<<< SEARCH')) return 'search-replace';
  for (let i = 0; i < lines.length; i += 1) {
    const line = lines[i]!;
    if (line.startsWith('diff --git ')) return 'unified';
    if (line.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')) return 'unified';
  }
  return null;
}

function stripRightSpaceTab(s: string): string {
  return s.replace(/[ \t]+$/, '');
}

function stripBothSpaceTab(s: string): string {
  return s.replace(/^[ \t]+|[ \t]+$/g, '');
}

function leadingSpaceTab(s: string): string {
  const match = /^[ \t]*/.exec(s);
  return match === null ? '' : match[0];
}

function normalizeForTier(line: string, tier: MatchTier): string {
  if (tier === 0) return line;
  if (tier === 1) return stripRightSpaceTab(line);
  return stripBothSpaceTab(line);
}

function normalizedSliceMatches(normFile: string[], pos: number, normPattern: string[]): boolean {
  for (let j = 0; j < normPattern.length; j += 1) {
    if (normFile[pos + j] !== normPattern[j]) return false;
  }
  return true;
}

function findPattern(
  fileLines: string[],
  pattern: string[],
  strict: boolean,
  minPos = 0,
  onlyPos?: number,
): { tier: MatchTier; positions: number[] } | null {
  const maxTier: MatchTier = strict ? 0 : 2;
  if (onlyPos !== undefined) {
    if (onlyPos < minPos || onlyPos < 0 || onlyPos + pattern.length > fileLines.length) return null;
    for (let t = 0; t <= maxTier; t += 1) {
      const tier = t as MatchTier;
      let ok = true;
      for (let j = 0; j < pattern.length; j += 1) {
        if (normalizeForTier(fileLines[onlyPos + j]!, tier) !== normalizeForTier(pattern[j]!, tier)) {
          ok = false;
          break;
        }
      }
      if (ok) return { tier, positions: [onlyPos] };
    }
    return null;
  }

  const lastStart = fileLines.length - pattern.length;
  if (minPos > lastStart) return null;

  for (let t = 0; t <= maxTier; t += 1) {
    const tier = t as MatchTier;
    const normFile = tier === 0 ? fileLines : fileLines.map((l) => normalizeForTier(l, tier));
    const normPattern = tier === 0 ? pattern : pattern.map((l) => normalizeForTier(l, tier));
    const positions: number[] = [];
    for (let pos = minPos; pos <= lastStart; pos += 1) {
      if (normalizedSliceMatches(normFile, pos, normPattern)) {
        positions.push(pos);
      }
    }
    if (positions.length > 0) return { tier, positions };
  }
  return null;
}

function reindentAddedLine(line: string, fileLead: string, patchLead: string): string {
  if (line.trim() !== '' && line.startsWith(patchLead)) {
    return fileLead + line.slice(patchLead.length);
  }
  return line;
}

function materializeBodyReplacement(
  items: BodyItem[],
  fileLines: string[],
  matchPos: number,
  firstOldLine: string,
  tier: MatchTier,
): string[] {
  const fileLead = leadingSpaceTab(fileLines[matchPos]!);
  const patchLead = leadingSpaceTab(firstOldLine);
  const out: string[] = [];
  let oldIdx = 0;
  for (const item of items) {
    if (item.kind === 'ctx') {
      out.push(fileLines[matchPos + oldIdx]!);
      oldIdx += 1;
    } else if (item.kind === 'del') {
      oldIdx += 1;
    } else {
      out.push(tier === 2 ? reindentAddedLine(item.text, fileLead, patchLead) : item.text);
    }
  }
  return out;
}

function materializePlainReplacement(
  newLines: string[],
  fileLines: string[],
  matchPos: number,
  firstOldLine: string,
  tier: MatchTier,
): string[] {
  if (tier !== 2) return [...newLines];
  const fileLead = leadingSpaceTab(fileLines[matchPos]!);
  const patchLead = leadingSpaceTab(firstOldLine);
  return newLines.map((line) => reindentAddedLine(line, fileLead, patchLead));
}

function parseDiffGitLine(line: string): [string, string] | null {
  if (!line.startsWith('diff --git a/')) return null;
  const rest = line.slice('diff --git a/'.length);
  const candidates: Array<[string, string]> = [];
  for (let idx = rest.indexOf(' b/'); idx >= 0; idx = rest.indexOf(' b/', idx + 1)) {
    const oldPart = rest.slice(0, idx);
    const newPart = rest.slice(idx + 3);
    if (
      oldPart !== '' &&
      newPart !== '' &&
      oldPart === oldPart.trim() &&
      newPart === newPart.trim()
    ) {
      candidates.push([oldPart, newPart]);
    }
  }
  if (candidates.length === 0) return null;
  const equalPair = candidates.find(([a, b]) => a === b);
  return equalPair ?? candidates[0]!;
}

function parseUnifiedHeaderPath(line: string): string {
  let raw = line.slice(4);
  const tabIdx = raw.indexOf('\t');
  if (tabIdx >= 0) raw = raw.slice(0, tabIdx);
  raw = raw.trim();
  if (raw === '/dev/null') return '/dev/null';
  if (raw.startsWith('a/') || raw.startsWith('b/')) return raw.slice(2);
  return raw;
}

function parseUnifiedEdits(lines: string[], strict: boolean): EditFn[] {
  const sections: UnifiedSection[] = [];
  let current: UnifiedSection | null = null;
  let inHeader = false;
  let hasDashPair = false;

  let i = 0;
  while (i < lines.length) {
    const line = lines[i]!;

    if (line === 'diff --git' || line.startsWith('diff --git ')) {
      const parsed = parseDiffGitLine(line);
      if (parsed === null) throw new Exit2Error(`error: parse ${i + 1}`);
      current = {
        gitOld: parsed[0],
        gitNew: parsed[1],
        minusPath: null,
        plusPath: null,
        renameFrom: null,
        renameTo: null,
        isNewFile: false,
        isDeletedFile: false,
        hunks: [],
      };
      sections.push(current);
      inHeader = true;
      hasDashPair = false;
      i += 1;
      continue;
    }

    if (line.startsWith('--- ')) {
      const next = lines[i + 1];
      if (next !== undefined && next.startsWith('+++ ')) {
        const minusPath = parseUnifiedHeaderPath(line);
        const plusPath = parseUnifiedHeaderPath(next);
        if (current !== null && inHeader && !hasDashPair) {
          current.minusPath = minusPath;
          current.plusPath = plusPath;
          hasDashPair = true;
        } else {
          current = {
            gitOld: null,
            gitNew: null,
            minusPath,
            plusPath,
            renameFrom: null,
            renameTo: null,
            isNewFile: false,
            isDeletedFile: false,
            hunks: [],
          };
          sections.push(current);
          inHeader = true;
          hasDashPair = true;
        }
        i += 2;
        continue;
      }
      if (current !== null && inHeader) {
        throw new Exit2Error(`error: parse ${i + 2}`);
      }
      i += 1;
      continue;
    }

    if (line.startsWith('@@')) {
      if (current === null) throw new Exit2Error(`error: parse ${i + 1}`);
      const hunkHeader = /^@@ -(\d+)(?:,\d+)? \+(\d+)(?:,\d+)? @@/.exec(line);
      if (hunkHeader === null) throw new Exit2Error(`error: parse ${i + 1}`);
      const oldStart = Number(hunkHeader[1]);
      inHeader = false;
      i += 1;

      const rawBody: Array<{ raw: string; kind: 'ctx' | 'del' | 'add' | 'noeol'; text: string }> = [];
      while (i < lines.length) {
        const bodyLine = lines[i]!;
        if (bodyLine === 'diff --git' || bodyLine.startsWith('diff --git ')) break;
        if (bodyLine.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')) break;
        if (bodyLine === '') {
          rawBody.push({ raw: '', kind: 'ctx', text: '' });
        } else if (bodyLine[0] === ' ') {
          rawBody.push({ raw: bodyLine, kind: 'ctx', text: bodyLine.slice(1) });
        } else if (bodyLine[0] === '-') {
          rawBody.push({ raw: bodyLine, kind: 'del', text: bodyLine.slice(1) });
        } else if (bodyLine[0] === '+') {
          rawBody.push({ raw: bodyLine, kind: 'add', text: bodyLine.slice(1) });
        } else if (bodyLine[0] === '\\') {
          rawBody.push({ raw: bodyLine, kind: 'noeol', text: bodyLine });
        } else {
          break;
        }
        i += 1;
      }

      while (rawBody.length > 0 && rawBody[rawBody.length - 1]!.raw === '') {
        rawBody.pop();
      }

      const items: BodyItem[] = [];
      for (const entry of rawBody) {
        if (entry.kind === 'noeol') {
          if (items.length > 0) items[items.length - 1]!.noEol = true;
        } else {
          items.push({ kind: entry.kind, text: entry.text, noEol: false });
        }
      }
      current.hunks.push({ oldStart, items });
      continue;
    }

    if (current !== null && inHeader) {
      if (line.startsWith('rename from ')) {
        current.renameFrom = line.slice('rename from '.length).trim();
      } else if (line.startsWith('rename to ')) {
        current.renameTo = line.slice('rename to '.length).trim();
      } else if (line === 'new file mode' || line.startsWith('new file mode ')) {
        current.isNewFile = true;
      } else if (line === 'deleted file mode' || line.startsWith('deleted file mode ')) {
        current.isDeletedFile = true;
      }
    }
    i += 1;
  }

  return sections.map((sec): EditFn => {
    const oldPath = sec.minusPath ?? sec.renameFrom ?? sec.gitOld ?? '';
    const newPath = sec.plusPath ?? sec.renameTo ?? sec.gitNew ?? '';

    const applyHunksToDoc = (doc: TextDocument, errPath: string): void => {
      let delta = 0;
      for (const hunk of sec.hunks) {
        const oldLines = hunk.items.filter((it) => it.kind !== 'add').map((it) => it.text);
        const newCount = hunk.items.filter((it) => it.kind !== 'del').length;

        let lastNewNoEol = false;
        for (let k = hunk.items.length - 1; k >= 0; k -= 1) {
          const it = hunk.items[k]!;
          if (it.kind === 'ctx' || it.kind === 'add') {
            lastNewNoEol = it.noEol;
            break;
          }
        }

        if (oldLines.length === 0) {
          const addLines = hunk.items.filter((it) => it.kind === 'add').map((it) => it.text);
          const rawPos = hunk.oldStart + delta;
          const insertPos = Math.max(0, Math.min(doc.lines.length, rawPos));
          const atEnd = insertPos === doc.lines.length;
          doc.lines.splice(insertPos, 0, ...addLines);
          if (atEnd && newCount > 0) doc.endsWithBreak = !lastNewNoEol;
        } else {
          const found = findPattern(doc.lines, oldLines, strict);
          if (found === null) throw new EditFailure('no-match', errPath);
          const target = hunk.oldStart - 1 + delta;
          let chosen = found.positions[0]!;
          let bestDist = Math.abs(chosen - target);
          for (let pIdx = 1; pIdx < found.positions.length; pIdx += 1) {
            const candidate = found.positions[pIdx]!;
            const dist = Math.abs(candidate - target);
            if (dist < bestDist) {
              chosen = candidate;
              bestDist = dist;
            }
          }
          const atEnd = chosen + oldLines.length === doc.lines.length;
          const replacement = materializeBodyReplacement(hunk.items, doc.lines, chosen, oldLines[0]!, found.tier);
          doc.lines.splice(chosen, oldLines.length, ...replacement);
          if (atEnd) doc.endsWithBreak = !lastNewNoEol;
        }

        delta += newCount - oldLines.length;
      }
    };

    if (oldPath === '/dev/null' || sec.isNewFile) {
      return (tree) => {
        if (!isSafePath(newPath)) throw new EditFailure('unsafe', newPath);
        if (tree.get(newPath) !== null) throw new EditFailure('exists', newPath);
        const addedItems: BodyItem[] = [];
        for (const hunk of sec.hunks) {
          for (const it of hunk.items) {
            if (it.kind === 'add') addedItems.push(it);
          }
        }
        const noFinalBreak = addedItems.length > 0 && addedItems[addedItems.length - 1]!.noEol;
        const content = joinDocument({
          lines: addedItems.map((it) => it.text),
          lineBreak: '\n',
          endsWithBreak: !noFinalBreak,
        });
        tree.set(newPath, content);
      };
    }

    if (newPath === '/dev/null' || sec.isDeletedFile) {
      return (tree) => {
        if (!isSafePath(oldPath)) throw new EditFailure('unsafe', oldPath);
        if (tree.get(oldPath) === null) throw new EditFailure('missing', oldPath);
        tree.remove(oldPath);
      };
    }

    if (oldPath !== newPath) {
      return (tree) => {
        if (!isSafePath(oldPath)) throw new EditFailure('unsafe', oldPath);
        if (!isSafePath(newPath)) throw new EditFailure('unsafe', newPath);
        const before = tree.get(oldPath);
        if (before === null) throw new EditFailure('missing', oldPath);
        if (tree.get(newPath) !== null) throw new EditFailure('exists', newPath);
        const doc = splitDocument(before);
        applyHunksToDoc(doc, oldPath);
        tree.remove(oldPath);
        tree.set(newPath, joinDocument(doc));
        tree.recordMove(oldPath, newPath);
      };
    }

    return (tree) => {
      if (!isSafePath(oldPath)) throw new EditFailure('unsafe', oldPath);
      const before = tree.get(oldPath);
      if (before === null) throw new EditFailure('missing', oldPath);
      const doc = splitDocument(before);
      applyHunksToDoc(doc, oldPath);
      tree.set(oldPath, joinDocument(doc));
    };
  });
}

function parseSearchReplaceEdits(lines: string[], strict: boolean): EditFn[] {
  const edits: EditFn[] = [];
  let prevEnd = -1;
  let prevPath: string | null = null;
  let i = 0;

  while (i < lines.length) {
    if (lines[i]!.trimEnd() !== '<<<<<<< SEARCH') {
      i += 1;
      continue;
    }

    const searchIdx = i;
    let foundPath: string | null = null;
    for (let k = searchIdx - 1; k > prevEnd; k -= 1) {
      const trimmed = lines[k]!.trim();
      if (trimmed !== '' && !trimmed.startsWith('```')) {
        foundPath = trimmed;
        break;
      }
    }

    const targetPath = foundPath ?? prevPath;
    if (targetPath === null) throw new Exit2Error(`error: parse ${searchIdx + 1}`);

    let sepIdx = -1;
    for (let j = searchIdx + 1; j < lines.length; j += 1) {
      if (lines[j]!.trimEnd() === '=======') {
        sepIdx = j;
        break;
      }
    }
    if (sepIdx < 0) throw new Exit2Error(`error: parse ${searchIdx + 1}`);

    let endIdx = -1;
    for (let k = sepIdx + 1; k < lines.length; k += 1) {
      if (lines[k]!.trimEnd() === '>>>>>>> REPLACE') {
        endIdx = k;
        break;
      }
    }
    if (endIdx < 0) throw new Exit2Error(`error: parse ${searchIdx + 1}`);

    const oldLines = lines.slice(searchIdx + 1, sepIdx);
    const newLines = lines.slice(sepIdx + 1, endIdx);

    prevPath = targetPath;
    prevEnd = endIdx;
    i = endIdx + 1;

    edits.push((tree) => {
      if (!isSafePath(targetPath)) throw new EditFailure('unsafe', targetPath);
      if (oldLines.length === 0) {
        if (tree.get(targetPath) !== null) throw new EditFailure('exists', targetPath);
        tree.set(targetPath, joinDocument({ lines: newLines, lineBreak: '\n', endsWithBreak: true }));
        return;
      }
      const before = tree.get(targetPath);
      if (before === null) throw new EditFailure('missing', targetPath);
      const doc = splitDocument(before);
      const found = findPattern(doc.lines, oldLines, strict);
      if (found === null) throw new EditFailure('no-match', targetPath);
      if (found.positions.length > 1) throw new EditFailure('ambiguous', targetPath);
      const pos = found.positions[0]!;
      const replacement = materializePlainReplacement(newLines, doc.lines, pos, oldLines[0]!, found.tier);
      doc.lines.splice(pos, oldLines.length, ...replacement);
      tree.set(targetPath, joinDocument(doc));
    });
  }

  return edits;
}

function isV4aSectionHeader(line: string): boolean {
  return (
    line.startsWith('*** Add File: ') ||
    line.startsWith('*** Delete File: ') ||
    line.startsWith('*** Update File: ')
  );
}

function parseV4aEdits(lines: string[], strict: boolean): EditFn[] {
  const firstNonBlank = lines.findIndex((line) => !isBlank(line));
  if (firstNonBlank < 0) throw new Exit2Error('error: parse 1');
  if (lines[firstNonBlank]!.trim() !== '*** Begin Patch') {
    throw new Exit2Error(`error: parse ${firstNonBlank + 1}`);
  }

  let lastNonBlank = lines.length - 1;
  while (lastNonBlank >= 0 && isBlank(lines[lastNonBlank]!)) lastNonBlank -= 1;
  if (lastNonBlank <= firstNonBlank || lines[lastNonBlank]!.trim() !== '*** End Patch') {
    throw new Exit2Error(`error: parse ${lines.length + 1}`);
  }

  const edits: EditFn[] = [];
  let i = firstNonBlank + 1;

  while (i < lastNonBlank) {
    while (i < lastNonBlank && isBlank(lines[i]!)) i += 1;
    if (i >= lastNonBlank) break;

    const headerIdx = i;
    const header = lines[headerIdx]!;
    if (!isV4aSectionHeader(header)) {
      throw new Exit2Error(`error: parse ${headerIdx + 1}`);
    }

    const bodyStart = headerIdx + 1;
    let bodyEnd = bodyStart;
    while (bodyEnd < lastNonBlank && !isV4aSectionHeader(lines[bodyEnd]!)) {
      bodyEnd += 1;
    }

    let trimmedEnd = bodyEnd;
    while (trimmedEnd > bodyStart && isBlank(lines[trimmedEnd - 1]!)) {
      trimmedEnd -= 1;
    }

    i = bodyEnd;

    if (header.startsWith('*** Add File: ')) {
      const targetPath = header.slice('*** Add File: '.length).trim();
      const fileLines: string[] = [];
      for (let k = bodyStart; k < trimmedEnd; k += 1) {
        const line = lines[k]!;
        if (line.startsWith('+')) fileLines.push(line.slice(1));
        else if (line === '') fileLines.push('');
        else throw new Exit2Error(`error: parse ${k + 1}`);
      }
      edits.push((tree) => {
        if (!isSafePath(targetPath)) throw new EditFailure('unsafe', targetPath);
        if (tree.get(targetPath) !== null) throw new EditFailure('exists', targetPath);
        tree.set(targetPath, joinDocument({ lines: fileLines, lineBreak: '\n', endsWithBreak: true }));
      });
      continue;
    }

    if (header.startsWith('*** Delete File: ')) {
      const targetPath = header.slice('*** Delete File: '.length).trim();
      if (trimmedEnd > bodyStart) {
        let badIdx = bodyStart;
        while (badIdx < trimmedEnd && isBlank(lines[badIdx]!)) badIdx += 1;
        throw new Exit2Error(`error: parse ${badIdx + 1}`);
      }
      edits.push((tree) => {
        if (!isSafePath(targetPath)) throw new EditFailure('unsafe', targetPath);
        if (tree.get(targetPath) === null) throw new EditFailure('missing', targetPath);
        tree.remove(targetPath);
      });
      continue;
    }

    // *** Update File: <path>
    const targetPath = header.slice('*** Update File: '.length).trim();
    let moveTo: string | null = null;
    let k = bodyStart;
    if (k < trimmedEnd && lines[k]!.startsWith('*** Move to: ')) {
      moveTo = lines[k]!.slice('*** Move to: '.length).trim();
      k += 1;
    }

    const chunks: V4aChunk[] = [];
    let currentChunk: V4aChunk | null = null;
    while (k < trimmedEnd) {
      const line = lines[k]!;
      if (line.startsWith('@@')) {
        const anchorText = line.slice(2).trim();
        currentChunk = { anchor: anchorText === '' ? null : anchorText, items: [], eof: false };
        chunks.push(currentChunk);
      } else if (line.trimEnd() === '*** End of File') {
        if (currentChunk === null) throw new Exit2Error(`error: parse ${k + 1}`);
        currentChunk.eof = true;
        currentChunk = null;
      } else if (line === '' || line[0] === ' ' || line[0] === '-' || line[0] === '+') {
        if (currentChunk === null) {
          if (chunks.length > 0) throw new Exit2Error(`error: parse ${k + 1}`);
          currentChunk = { anchor: null, items: [], eof: false };
          chunks.push(currentChunk);
        }
        if (line === '') {
          currentChunk.items.push({ kind: 'ctx', text: '', noEol: false });
        } else if (line[0] === ' ') {
          currentChunk.items.push({ kind: 'ctx', text: line.slice(1), noEol: false });
        } else if (line[0] === '-') {
          currentChunk.items.push({ kind: 'del', text: line.slice(1), noEol: false });
        } else {
          currentChunk.items.push({ kind: 'add', text: line.slice(1), noEol: false });
        }
      } else {
        throw new Exit2Error(`error: parse ${k + 1}`);
      }
      k += 1;
    }

    if (chunks.length === 0 && moveTo === null) {
      throw new Exit2Error(`error: parse ${headerIdx + 1}`);
    }

    edits.push((tree) => {
      if (!isSafePath(targetPath)) throw new EditFailure('unsafe', targetPath);
      if (moveTo !== null && !isSafePath(moveTo)) throw new EditFailure('unsafe', moveTo);
      const before = tree.get(targetPath);
      if (before === null) throw new EditFailure('missing', targetPath);
      if (moveTo !== null && tree.get(moveTo) !== null) throw new EditFailure('exists', moveTo);

      const doc = splitDocument(before);
      let cursor = 0;

      for (const chunk of chunks) {
        if (chunk.anchor !== null) {
          const anchorMatch = findPattern(doc.lines, [chunk.anchor], strict, cursor);
          if (anchorMatch === null) throw new EditFailure('no-match', targetPath);
          cursor = anchorMatch.positions[0]! + 1;
        }

        const oldLines = chunk.items.filter((it) => it.kind !== 'add').map((it) => it.text);
        if (oldLines.length === 0) {
          const addLines = chunk.items.filter((it) => it.kind === 'add').map((it) => it.text);
          const insertPos = chunk.eof ? doc.lines.length : cursor;
          doc.lines.splice(insertPos, 0, ...addLines);
          cursor = insertPos + addLines.length;
        } else {
          const found = chunk.eof
            ? findPattern(doc.lines, oldLines, strict, cursor, doc.lines.length - oldLines.length)
            : findPattern(doc.lines, oldLines, strict, cursor);
          if (found === null) throw new EditFailure('no-match', targetPath);
          const pos = found.positions[0]!;
          const replacement = materializeBodyReplacement(chunk.items, doc.lines, pos, oldLines[0]!, found.tier);
          doc.lines.splice(pos, oldLines.length, ...replacement);
          cursor = pos + replacement.length;
        }
      }

      const after = joinDocument(doc);
      if (moveTo !== null) {
        tree.remove(targetPath);
        tree.set(moveTo, after);
        tree.recordMove(targetPath, moveTo);
      } else {
        tree.set(targetPath, after);
      }
    });
  }

  return edits;
}

function buildJsonEdit(value: unknown): EditFn | null {
  if (value === null || typeof value !== 'object' || Array.isArray(value)) return null;
  const obj = value as Record<string, unknown>;
  const targetPath = obj.path;
  if (typeof targetPath !== 'string') return null;

  const requireExisting = (tree: VirtualTree): string => {
    if (!isSafePath(targetPath)) throw new EditFailure('unsafe', targetPath);
    const current = tree.get(targetPath);
    if (current === null) throw new EditFailure('missing', targetPath);
    return current;
  };

  if (obj.command === 'create' && typeof obj.file_text === 'string') {
    const fileText = obj.file_text;
    return (tree) => {
      if (!isSafePath(targetPath)) throw new EditFailure('unsafe', targetPath);
      if (tree.get(targetPath) !== null) throw new EditFailure('exists', targetPath);
      tree.set(targetPath, fileText);
    };
  }

  if (
    obj.command === 'str_replace' &&
    typeof obj.old_str === 'string' &&
    obj.old_str !== '' &&
    (obj.new_str === undefined || typeof obj.new_str === 'string')
  ) {
    const oldStr = obj.old_str;
    const newStr = (obj.new_str as string | undefined) ?? '';
    return (tree) => {
      const before = requireExisting(tree);
      const firstLf = before.indexOf('\n');
      const isCrlf = firstLf > 0 && before[firstLf - 1] === '\r';
      const toLf = (s: string): string => (isCrlf ? s.replaceAll('\r\n', '\n') : s);
      const hay = toLf(before);
      const needle = toLf(oldStr);
      let firstAt = -1;
      let count = 0;
      for (let pos = hay.indexOf(needle); pos >= 0; pos = hay.indexOf(needle, pos + 1)) {
        if (firstAt < 0) firstAt = pos;
        count += 1;
      }
      if (count === 0) throw new EditFailure('no-match', targetPath);
      if (count > 1) throw new EditFailure('ambiguous', targetPath);
      const replaced = hay.slice(0, firstAt) + toLf(newStr) + hay.slice(firstAt + needle.length);
      tree.set(targetPath, isCrlf ? replaced.replaceAll('\n', '\r\n') : replaced);
    };
  }

  if (
    obj.command === 'insert' &&
    typeof obj.insert_line === 'number' &&
    Number.isInteger(obj.insert_line) &&
    typeof obj.new_str === 'string'
  ) {
    const insertLine = obj.insert_line;
    const addLines = splitPatchLines(obj.new_str);
    return (tree) => {
      const before = requireExisting(tree);
      const doc = splitDocument(before);
      if (insertLine < 0 || insertLine > doc.lines.length) {
        throw new EditFailure('no-match', targetPath);
      }
      doc.lines.splice(insertLine, 0, ...addLines);
      tree.set(targetPath, joinDocument(doc));
    };
  }

  return null;
}

function parseJsonEdits(text: string, lines: string[]): EditFn[] {
  const firstNonBlank = lines.findIndex((line) => !isBlank(line));
  if (firstNonBlank < 0) throw new Exit2Error('error: parse 1');

  if (lines[firstNonBlank]!.trimStart().startsWith('[')) {
    let parsed: unknown;
    try {
      parsed = JSON.parse(text);
    } catch {
      throw new Exit2Error(`error: parse ${firstNonBlank + 1}`);
    }
    if (!Array.isArray(parsed)) {
      throw new Exit2Error(`error: parse ${firstNonBlank + 1}`);
    }
    const edits: EditFn[] = [];
    for (const item of parsed) {
      const edit = buildJsonEdit(item);
      if (edit === null) throw new Exit2Error(`error: parse ${firstNonBlank + 1}`);
      edits.push(edit);
    }
    return edits;
  }

  const edits: EditFn[] = [];
  for (let i = 0; i < lines.length; i += 1) {
    const line = lines[i]!;
    if (isBlank(line)) continue;
    let edit: EditFn | null = null;
    try {
      edit = buildJsonEdit(JSON.parse(line));
    } catch {
      edit = null;
    }
    if (edit === null) throw new Exit2Error(`error: parse ${i + 1}`);
    edits.push(edit);
  }
  return edits;
}

function parsePatch(format: ConcreteFormat, text: string, lines: string[], strict: boolean): EditFn[] {
  if (format === 'unified') return parseUnifiedEdits(lines, strict);
  if (format === 'search-replace') return parseSearchReplaceEdits(lines, strict);
  if (format === 'v4a') return parseV4aEdits(lines, strict);
  return parseJsonEdits(text, lines);
}

function runCli(args: string[]): { code: number; out: string[] } {
  let formatOpt: PatchFormat | null = null;
  let checkOnly = false;
  let strict = false;
  let optionsEnded = false;
  const positional: string[] = [];

  for (const arg of args) {
    if (!optionsEnded && arg === '--') {
      optionsEnded = true;
    } else if (!optionsEnded && arg.startsWith('-') && arg !== '-') {
      if (arg.startsWith('--format=') && formatOpt === null) {
        const name = arg.slice('--format='.length);
        if (!VALID_FORMATS.has(name)) return { code: 2, out: ['error: usage'] };
        formatOpt = name as PatchFormat;
      } else if (arg === '--check' && !checkOnly) {
        checkOnly = true;
      } else if (arg === '--strict' && !strict) {
        strict = true;
      } else {
        return { code: 2, out: ['error: usage'] };
      }
    } else {
      positional.push(arg);
    }
  }

  if (positional.length > 1) return { code: 2, out: ['error: usage'] };

  const patchPath = positional.length === 0 || positional[0] === '-' ? null : positional[0]!;
  let patchText = '';
  try {
    patchText = readFileSync(patchPath ?? 0, 'utf8');
  } catch {
    if (patchPath !== null) return { code: 2, out: ['error: no-patch'] };
  }

  const lines = splitPatchLines(patchText);
  const resolvedFormat: ConcreteFormat | null =
    formatOpt === null || formatOpt === 'auto' ? detectFormat(lines) : formatOpt;
  if (resolvedFormat === null) return { code: 2, out: ['error: format'] };

  let edits: EditFn[];
  try {
    edits = parsePatch(resolvedFormat, patchText, lines, strict);
    if (edits.length === 0) throw new Exit2Error('error: parse 1');
  } catch (err) {
    if (err instanceof Exit2Error) return { code: 2, out: [err.message] };
    throw err;
  }

  const tree = new VirtualTree();
  const failures: EditFailure[] = [];

  for (const edit of edits) {
    const savedOverlay = new Map(tree.overlay);
    const savedMoves = new Map(tree.movedFrom);
    try {
      edit(tree);
    } catch (err) {
      if (!(err instanceof EditFailure)) throw err;
      tree.overlay.clear();
      for (const [k, v] of savedOverlay) tree.overlay.set(k, v);
      tree.movedFrom.clear();
      for (const [k, v] of savedMoves) tree.movedFrom.set(k, v);
      failures.push(err);
    }
  }

  if (failures.length > 0) {
    return {
      code: 1,
      out: [
        ...failures.map((f) => `error: ${f.code} ${f.path}`),
        `failed: ${failures.length} of ${edits.length} edits`,
      ],
    };
  }

  const added = new Set<string>();
  const deleted = new Set<string>();
  const modified = new Set<string>();

  for (const [p, nowContent] of tree.overlay) {
    const origContent = tree.original(p);
    if (origContent === nowContent) continue;
    if (origContent === null) added.add(p);
    else if (nowContent === null) deleted.add(p);
    else modified.add(p);
  }

  if (!checkOnly) {
    for (const p of [...deleted].sort(utf8ByteCompare)) {
      rmSync(p, { force: true });
    }
    for (const p of [...added, ...modified].sort(utf8ByteCompare)) {
      mkdirSync(dirname(p), { recursive: true });
      writeFileSync(p, tree.overlay.get(p)!);
    }
  }

  const summaryRows: Array<[string, string]> = [];
  for (const [toPath, fromPath] of tree.movedFrom) {
    if (deleted.has(fromPath) && added.has(toPath)) {
      deleted.delete(fromPath);
      added.delete(toPath);
      summaryRows.push([toPath, `R ${fromPath} -> ${toPath}`]);
    }
  }
  for (const p of added) summaryRows.push([p, `A ${p}`]);
  for (const p of deleted) summaryRows.push([p, `D ${p}`]);
  for (const p of modified) summaryRows.push([p, `M ${p}`]);

  summaryRows.sort(([a], [b]) => utf8ByteCompare(a, b));
  const outLines = summaryRows.map(([, row]) => row);
  outLines.push(`ok: ${outLines.length} ${outLines.length === 1 ? 'file' : 'files'}`);
  return { code: 0, out: outLines };
}

const trialEnv = process.env.MAKEFUN_ENV_URL;
if (trialEnv !== undefined && trialEnv !== '') {
  const { runTrial } = await import('./runner.ts');
  await runTrial(trialEnv);
} else {
  const result = runCli(process.argv.slice(2));
  const outBuf = Buffer.from(result.out.map((line) => `${line}\n`).join(''), 'utf8');
  let offset = 0;
  while (offset < outBuf.length) {
    offset += writeSync(1, outBuf, offset, outBuf.length - offset);
  }
  process.exitCode = result.code;
}
