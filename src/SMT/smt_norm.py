from z3 import *
import numpy as np
import time
from glob import glob, has_magic

def max_v(v):
    max = v[0]
    for value in v[1:]:
        max = If(value > max, value, max)
    return max

filein = "./instances/ins-1.txt"
search="normal"

fi=[]
if not os.path.exists("./"+search+"/out"):
    os.makedirs("./"+search+"/out")

fin=filein.split('/')[-1]
dirin=filein[:filein.rfind('/')]
if fin=='*':
    allf=glob(os.path.join(dirin, '*.txt'))
    for i in range(len(allf)):
        fi.append(i + 1)
else:
    fi.append(fin[fin.find('-')+1:fin.find('.')])
#print(fi)
for f in fi:
    print(f)
    fileout= os.path.join("./"+search+"/out", "out-"+str(f)+".txt")
    with open(dirin+"/ins-"+str(f)+".txt","r") as file:
        w = int(file.readline())
        n = int(file.readline())
        #print (w)
        #print (n)
        x = [Int('x_%s' % i) for i in range(n)]
        y = [Int('y_%s' % i) for i in range(n)]
        lc= []
        hc= []
        for r in file:
            b = r.rstrip().split(" ")
            lc.append(int(b[0]))
            hc.append(int(b[1]))
        #print(lc)
        #print(hc)
        hmax=sum(hc)-min(hc)
        wmax=sum(lc)-min(lc)

        #objective function
        H=max_v([y[i]+hc[i] for i in range(n)])

        # main constraints
        c1=[If(i==j,
                True,
                Or(Or(x[i]+str(lc[i])<=x[j],x[j]+str(lc[j])<=x[i]),Or(y[i]+str(hc[i])<=y[j],y[j]+str(hc[j])<=y[i])))
                for i in range(n) for j in range(n)]
        #print(c1)
        #c2=[And(And(x[i]>=0,x[i]<=wmax),And(y[i]>=0,y[i]<=hmax)) for i in range(n)]
        c2=[And(x[i]>=0,y[i]>=0) for i in range(n)]
        c3=[And(x[i]+lc[i]<=w,y[i]+hc[i]<=H) for i in range(n)]
 
        #implied constraints
        c4=[sum([If(And(y[i]+hc[i]>k,y[i]<=k),lc[i],0) for i in range(n)])<=w for k in range(hmax)]
        c5=[sum([If(And(x[i]+lc[i]>k,x[i]<=k),hc[i],0) for i in range(n)])<=H for k in range(wmax)]
    
        #symmetry cinstraints
        ind=np.argmax([lc[i]*hc[i]  for i in range(n)])
        c6=[And(x[ind]==0,y[ind]==0)]

    #solve(c1+c2+c3)
    opt=Optimize()
    opt.add(c1+c2+c3+c4+c5+c6)
    opt.minimize(H)
    opt.set("timeout", 300000)
    ris=opt.check()
    if ris == sat:
        fo=open(fileout,"w")
        print("SAT")
        m=opt.model()
        h=m.evaluate(H).as_string()
        fo.write(str(w)+" "+str(h)+"\n")
        print(str(w)+" "+str(h))
        fo.write(str(n)+"\n")
        print(n)
        for i in range(n):
            fo.write(str(lc[i])+" "+str(hc[i])+" "+m.evaluate(x[i]).as_string()+" "+m.evaluate(y[i]).as_string()+"\n")
            print(str(lc[i])+" "+str(hc[i])+" "+m.evaluate(x[i]).as_string()+" "+m.evaluate(y[i]).as_string())
        fo.close()
    elif ris == unsat:
        fo=open(fileout,"w")
        fo.write("UNSAT")
        print("UNSAT")
        fo.close()
    else:
        fo=open(fileout,"w")
        fo.write("FAILED")
        print("FAILED")
        fo.close()
