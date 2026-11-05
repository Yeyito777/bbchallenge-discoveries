"""Helpers shared by the generators of the Rocq data files: integer arrays as Rocq array literals."""
CHUNK = 1 << 16  # integers per array chunk, as aget in Wang_Checker.v; larger literals overflow the native compiler's stack


def pack7(data):
    """Bytes to integers of 7 bytes each, low byte first (the checker's read_byte)."""
    return [int.from_bytes(data[i:i + 7], "little") for i in range(0, len(data), 7)]


def pack_tori(tori):
    """Tori as lists [a, b, s, cells...] to (tdata, toff): one integer a + 2^10 b + 2^20 s, then the
    cells, 16 to an integer, 3 bits each (grid_at in Wang_Checker.v)."""
    tdata, toff = [], []
    for t in tori:
        a, b, s, cells = t[0], t[1], t[2], t[3:]
        assert len(cells) == a * b and a < 1024 and b < 1024 and s < 1024 and all(0 <= x < 8 for x in cells)
        toff.append(len(tdata))
        tdata.append(a | b << 10 | s << 20)
        for i in range(0, len(cells), 16):
            w = 0
            for j, x in enumerate(cells[i:i + 16]):
                w |= x << (3 * j)
            tdata.append(w)
    return tdata, toff


def chunks(xs):
    return [xs[i:i + CHUNK] for i in range(0, len(xs), CHUNK)] or [[]]


def array_lit(xs):
    return "[| %s | 0 : int |]" % "; ".join(map(str, xs))


def outer_lit(names):
    return "[| %s | %s : array int |]" % ("; ".join(names), names[0])


def list_lit(xs, name, f, size=4000):
    """A long list of integers as a concatenation of definitions of at most [size] elements."""
    parts = []
    for i in range(0, len(xs), size):
        nm = "%s_%d" % (name, i // size)
        parts.append(nm)
        f.write("Definition %s : list int := [%s].\n" % (nm, ";".join(map(str, xs[i:i + size]))))
    return " ++ ".join(parts) if parts else "[]"


HEAD = "From Coq Require Import List Uint63 PArray.\n"  # no ListNotations: it breaks the [| |] syntax


def leb_tokens(data):
    """The LEB128 tokens of a certificate stream."""
    out, x, sh = [], 0, 0
    for b in data:
        x |= (b & 0x7F) << sh
        sh += 7
        if not b & 0x80:
            out.append(x)
            x = sh = 0
    assert sh == 0, "stream ends inside a token"
    return out


MAXLEN = 40   # longest code; the decoder in Wang_Checker.v tries at most this many bits
WBITS = 62    # bits per integer of the coded stream, most significant first


def huffman(tokens):
    """Canonical Huffman code of the tokens: (lengths dict, symbols in canonical order, counts per length)."""
    import heapq
    from collections import Counter
    freq = Counter(tokens)
    if len(freq) == 1:
        lens = {next(iter(freq)): 1}
    else:
        heap = [(f, i, (s,)) for i, (s, f) in enumerate(sorted(freq.items()))]
        heapq.heapify(heap)
        depth = dict.fromkeys(freq, 0)
        k = len(heap)
        while len(heap) > 1:
            f1, _, a = heapq.heappop(heap)
            f2, _, b = heapq.heappop(heap)
            for s in a + b:
                depth[s] += 1
            heapq.heappush(heap, (f1 + f2, k, a + b))
            k += 1
        lens = depth
    assert max(lens.values()) <= MAXLEN, "code too long"
    syms = sorted(lens, key=lambda s: (lens[s], s))
    counts = [0] * (MAXLEN + 1)
    for s in syms:
        counts[lens[s]] += 1
    return lens, syms, counts


def huffman_encode(tokens):
    """(integers of the coded stream, symbol table, counts per length 0..MAXLEN)."""
    lens, syms, counts = huffman(tokens)
    code, first, c = {}, 0, 0
    for L in range(1, MAXLEN + 1):
        for s in syms[c:c + counts[L]]:
            code[s] = first
            first += 1
        c += counts[L]
        first <<= 1
    words, acc, nb = [], 0, 0
    for t in tokens:
        L, v = lens[t], code[t]
        for i in range(L - 1, -1, -1):
            acc = (acc << 1) | ((v >> i) & 1)
            nb += 1
            if nb == WBITS:
                words.append(acc)
                acc, nb = 0, 0
    if nb:
        words.append(acc << (WBITS - nb))
    return words, syms, counts
