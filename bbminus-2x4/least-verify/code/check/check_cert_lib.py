def parse_machine(s):
    s = s.replace('_', '')
    t = {}
    for i in range(8):
        c = s[3*i:3*i+3]
        if c != '---':
            t[(i//4, i % 4)] = (int(c[0]), 1 if c[1] == 'R' else 0, ord(c[2])-65)
    return t

def parse_tape(s):
    i = s.index('[')
    return [int(c) for c in s[:i]], int(s[i+1]), [int(c) for c in s[i+3:]]
