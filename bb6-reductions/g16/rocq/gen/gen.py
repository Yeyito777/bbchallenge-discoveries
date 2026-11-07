# Writes theories/M01.v .. theories/M16.v from gen/table.txt: machine, mirror, a-state, f-state, c.
for i,line in enumerate(open('gen/table.txt')):
    M,mir,A,F,c=line.split()
    ID=f'M{i+1:02d}'
    lit='  etransitivity; [apply mirror_halts|exact main_tm].' if mir=='1' else '  exact main_tm.'
    t=open(f'gen/template{c}.v').read()
    t=(t.replace('@@M@@',M).replace('@@WRAP@@','mirror tm0' if mir=='1' else 'tm0')
        .replace('@@F@@',F).replace('@@A@@',A).replace('@@ID@@',ID).replace('@@LIT@@',lit))
    open(f'theories/{ID}.v','w').write(t)
