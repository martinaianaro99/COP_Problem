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

        rot = [Bool(f"r_{i}") for i in range(n)]

        # main constraints
        # set true variables in circuit area with area limits
        allc=[]
        for k in range(n):
            
            allck=[]
            allck1=[]
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
            """
            allck+=[If(And(i <= di,di<i + lcr[k],j<= dj,dj<j + hcr[k]),pc[di][dj][k],pc[di][dj][k]==False) for di in range(wmax) for dj in range(hmax)
                for i in range(wmax-lcr[k]+1) for j in range(hmax-hcr[k]+1)]
            """
            # constraint only one cistcuit valid
            #allc+=[If(i==j, True,Not(And(allck[i],allck[j]))) for i in range(len(allck)) for j in range(len(allck))]
            allck1+=[Not(And(pair[0],pair[1])) for pair in combinations(allck,2)]
            #constraint al least one circuit valid
            allck1+=[Or(allck)]
            allck1+=[Not(rot[k])]
            a=[And(allck1)]

            allckr=[]
            allckr1=[]
            for i in range(wmax - lc[k] + 1):
                for j in range(hmax - hc[k] + 1):

                        ck=[]
                        for dj in range(hmax):
                            for di in range(wmax):
                                if (j <= dj and dj<j + lc[k]) and (i <= di and di< i + hc[k]):
                                    ck.append(pc[di][dj][k])
                                else:
                                    ck.append(Not(pc[di][dj][k]))
                        # define each circuit
                        allckr.append(And(ck))
        
            # constraint only one cistcuit valid
            #allc+=[If(i==j, True,Not(And(allck[i],allck[j]))) for i in range(len(allck)) for j in range(len(allck))]
            allckr1+=[Not(And(pair[0],pair[1])) for pair in combinations(allckr,2)]
            #constraint al least one circuit valid
            allckr1+=[Or(allck)]
            #condition not rotation
            allckr1+=[rot[k]]
            ar=[And(allckr)]
           
            # constraint one circuit active
            a=a+ar
            allc+=[Not(And(pair[0],pair[1]))for pair in combinations(a,2)]
            allc+=[Or(a)]


        # constraint for assure no circuit overlapping
        c1=[If (k1==k2,True,Not(And(pc[i][j][k1],pc[i][j][k2])))
            for i in range(wmax) for j in range(hmax) for k1 in range(n) for k2 in range(n)]

        
         # define H variable true where index is plate total lengh minus one
        c2=[If (And(Or([pc[i][j][k] for i in range(wmax) for k in range(n)]),Not(Or([pc[i][j+dj+1][k] for i in range(wmax) for k in range(n)for dj in range(hmax-j-1)]))), H[j], H[j]==False)
                for j in range(hmax-1)]
            #condition for last H level
        c3=[If(Or([pc[i][j][k]  for i in range(wmax) for k in range(n)]), H[j], H[j]==False) for j in range((hmax-1),hmax)]
        
        # simmetry coinstraint-bigger circuit in the origin
        a=[lc[k]*hc[k] for k in range(n)]
        bc=np.argmax(a)
        #print(bc)
        c4=[pc[0][0][bc]]

        s=Solver()
        s.add(allc+c1+c2+c3+c4)
        s.set("timeout", 300000)
        ris=s.check()

        if ris == sat:
            fo=open(fileout,"w")
            print("SAT")
            m=s.model()
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
                #print(v)
                px.append(v[0][0])
                py.append(v[1][0])
                fo.write(str(lc[k])+" "+str(hc[k])+" "+str(px[k])+" "+str(py[k])+" "+str(m[rot[k]])+"\n")
                print(str(lc[k])+" "+str(hc[k])+" "+str(px[k])+" "+str(py[k])+" "+str(m.evaluate(rot[k])))
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