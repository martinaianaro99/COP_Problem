from z3 import *
import numpy as np
import time
from glob import glob, has_magic

def max_v(v):
    max = v[0]
    for value in v[1:]:
        max = If(value > max, value, max)
    return max

filein = "./instances/*"
search="rotation"

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
        rot = [Bool("rot_%s" %i) for i in range(n)]
        lc= []
        hc= []
        for r in file:
            b = r.rstrip().split(" ")
            lc.append(int(b[0]))
            hc.append(int(b[1]))

        hmax=sum(hc)-min(hc+lc)
        wmax=w-min(lc+hc)

        # boolean variables for circuits rotation  
        lcr = [If (rot[i], hc[i], lc[i]) for i in range(n)]
        hcr = [If (rot[i], lc[i], hc[i]) for i in range(n)]

        #objective function
        H=max_v([y[i]+hcr[i] for i in range(n)])

        # main constraints
        c1=[If(i==j,
                True,
                Or(Or(x[i]+lcr[i]<=x[j],x[j]+lcr[j]<=x[i]),Or(y[i]+hcr[i]<=y[j],y[j]+hcr[j]<=y[i])))
                for i in range(n) for j in range(n)]
        
        #c21=[And(x[i]<=wmax,y[i]<=hmax) for i in range(n)]
        c2=[And(x[i]>=0,y[i]>=0) for i in range(n)]
        c3=[And(x[i]+lcr[i]<=w,y[i]+hcr[i]<=H) for i in range(n)]
        c31=[If (hc[i]>w, rot[i]==False, True) for i in range(n)]
 
        #implied constraints
        c4=[sum([If(And(y[i]+hcr[i]>k,y[i]<=k),lcr[i],0) for i in range(n)])<=w for k in range(hmax)]
        c5=[sum([If(And(x[i]+lcr[i]>k,x[i]<=k),hcr[i],0) for i in range(n)])<=H for k in range(wmax)]
    
        #symmetry cinstraints
        ind=np.argmax([lc[i]*hc[i]  for i in range(n)])
        c6=[And(x[ind]==0,y[ind]==0)]

    #solve(c1+c2+c3)
    opt=Optimize()
    opt.add(c1+c2+c3+c4+c5+c6+c31)
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
            if m[rot[i]] is None:
                fo.write(str(lc[i])+" "+str(hc[i])+" "+m.evaluate(x[i]).as_string()+" "+m.evaluate(y[i]).as_string()+" "+"False"+"\n")
                print(str(lc[i])+" "+str(hc[i])+" "+m.evaluate(x[i]).as_string()+" "+m.evaluate(y[i]).as_string()+" "+"False")
            else:
                fo.write(str(lc[i])+" "+str(hc[i])+" "+m.evaluate(x[i]).as_string()+" "+m.evaluate(y[i]).as_string()+" "+str(m[rot[i]])+"\n")
                print(str(lc[i])+" "+str(hc[i])+" "+m.evaluate(x[i]).as_string()+" "+m.evaluate(y[i]).as_string()+" "+str(m[rot[i]]))
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