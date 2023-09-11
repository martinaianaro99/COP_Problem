from os import add_dll_directory
from z3 import *
import numpy as np
import time
from glob import glob, has_magic
from itertools import combinations

def max_v(v):
    max = v[0]
    for value in v[1:]:
        max = If(value > max, value, max)
    return max

#directory containing instances
filein = "./instances/*"
#problem model
search="normal"
fi=[]
#create the directory containing output
if not os.path.exists("../out/"+search+"/out"):
    os.makedirs("../out/"+search+"/out")

fin=filein.split('/')[-1]
dirin=filein[:filein.rfind('/')]
if fin=='*':
    allf=glob(os.path.join(dirin, '*.txt'))
    for i in range(len(allf)):
        fi.append(i + 1)
else:
    fi.append(fin[fin.find('-')+1:fin.find('.')])
    
#iterate over files containing instances to take instances data
for f in fi:
    print(f)
    fileout= os.path.join("../out/"+search+"/out", "out-"+str(f)+".txt")
    with open(dirin+"/ins-"+str(f)+".txt","r") as file:
        w = int(file.readline())
        n = int(file.readline())
        x = [Int('x_%s' % i) for i in range(n)]
        y = [Int('y_%s' % i) for i in range(n)]
        lc= []
        hc= []
        for r in file:
            b = r.rstrip().split(" ")
            lc.append(int(b[0]))
            hc.append(int(b[1]))
        
        hmax=sum(hc)
        wmax=w

        #3d matrix with boolean variable for each elemen in circuit area
        pc = [[[Bool(f"p_{i}_{j}_{k}") for k in range(n)] for j in range(hmax)] for i in range(wmax)]

        #boolean array indicating hmax- inde xof true variable is h value
        H = [Bool(f"l_{i}") for i in range(hmax)]
        
        # main constraints
        # set true variables in circuit area with area limits
        allc=[]
        for k in range(n):
            allck=[]
            
            for i in range(wmax - lc[k] + 1):
                for j in range(hmax - hc[k] + 1):

                        ck=[]
                        for dj in range(hmax):
                            for di in range(wmax):
                                if (j <= dj and dj<j + hc[k]) and (i <= di and di< i + lc[k]):
                                    ck.append(pc[di][dj][k])
                                else:
                                    ck.append(Not(pc[di][dj][k]))
                        # define each circuit
                        allck.append(And(ck))

            # constraint only one cistcuit valid
            allc+=[Not(And(pair[0],pair[1])) for pair in combinations(allck,2)]
            #constraint al least one circuit valid
            allc+=[Or(allck)]

        # constraint for assure no circuit overlapping
        c1=[If (k1==k2,True,Not(And(pc[i][j][k1],pc[i][j][k2])))
            for i in range(wmax) for j in range(hmax) for k1 in range(n) for k2 in range(n)]

        
         # define H variable true where index is plate total lengh minus one
        c2=[If (And(Or([pc[i][j][k] for i in range(wmax) for k in range(n)]),Not(Or([pc[i][j+dj+1][k] for i in range(wmax) for k in range(n)for dj in range(hmax-j-1)]))), H[j], H[j]==False)
                for j in range(hmax-1)]
            #condition for last H level
        c3=[If(Or([pc[i][j][k]  for i in range(wmax) for k in range(n)]), H[j], H[j]==False) for j in range((hmax-1),hmax)]
        
        # simmetry coinstraint-biggest circuit in the origin
        a=[lc[k]*hc[k] for k in range(n)]
        bc=np.argmax(a)
        c4=[pc[0][0][bc]]
        
        #computing solution
        s=Solver()
        s.add(allc+c1+c2+c3+c4)
        s.set("timeout", 300000)
        #checking the result
        c=False
        ris=sat
        #result is SAT
        while ris==sat:
            ris=s.check()
            if ris==sat:
                c=True
                m=s.model()
                for i in range(hmax):
                    if m.evaluate(H[i]):
                        ind=i
                s.add(Or([H[i]for i in range(ind)]))
        #result UNSAT and c=True
        if (ris == unsat and c):
            fo=open(fileout,"w")
            print("SAT")
            for i in range(hmax):
                if m.evaluate(H[i]):
                        h=i+1
            fo.write(str(w)+" "+str(h)+"\n")
            print(str(w)+" "+str(h))
            fo.write(str(n)+"\n")
            print(n)
            px=[]
            py=[]
            for k in range(n):
                ck=[[m.evaluate(pc[i][j][k]) for j in range(hmax)] for i in range(wmax)]
                v=np.where(ck)
                px.append(v[0][0])
                py.append(v[1][0])
                fo.write(str(lc[k])+" "+str(hc[k])+" "+str(px[k])+" "+str(py[k])+"\n")
                print(str(lc[k])+" "+str(hc[k])+" "+str(px[k])+" "+str(py[k]))
            fo.close()
         #result UNSAT and c=False           
        elif (ris == unsat and c==False):
            fo=open(fileout,"w")
            fo.write("UNSAT")
            print("UNSAT")
            fo.close()
        #result is Unknown
        else:
            fo=open(fileout,"w")
            fo.write("Unknown")
            print("Unknown")
            fo.close()