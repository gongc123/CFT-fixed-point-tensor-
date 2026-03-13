#!/usr/bin/env python
# coding: utf-8

# In[ ]:
import sympy, pickle, multiset, numpy,datetime,shelve,os
from sympy import Lambda, symbols, Symbol, simplify, Function, series, limit, expand, factor, factorial, latex, Wild, together, fraction,re,im,N
from multiset import Multiset, FrozenMultiset
from numpy import linalg

c=symbols('c')
h=symbols('h')
x,y,z,w=symbols('x y z w')
hl=symbols('h_1 h_2 h_3 h_4',integer=True)
hhl=symbols('hh_1 hh_2 hh_3 hh_4 hh_5 hh_6')
var=symbols('x y z w')
vardif=symbols('xd_1 xd_2 xd_3 xd_4 xd_5 xd_6')
varsub=symbols('xx yy zz ww')
f=Function('f')
sch=Function('Sch_f')(x)
schh=f(x).diff(x,3)/f(x).diff(x,1)-3 *(f(x).diff(x,2)/f(x).diff(x,1))**2/2
a,b=map(Wild,['a','b'])



def strsum(st):                   # return the sum of a string of numbers
    s=0
    for ele in st:
        s+=int(ele)
    return s
            
def sset(lis1):                   # return the set of strings {k'}<= lis1
    if lis1=='':
        return ['']
    ns=[]
    s=sset(lis1[1:])
    for n in range(int(lis1[0])+1):
        for ele in s:
            ns.append(str(n)+ele)
    return ns

def slset(lis1,lis2):            # return the set of strings  {k''} lies between lis1 and lis2
    if lis1=='':
        return ['']
    ns=[]
    s=slset(lis1[1:],lis2[1:])
    for n in range(int(lis2[0]),int(lis1[0])+1):
        for ele in s:
            ns.append(str(n)+ele)
    return ns
            
def sim(lis):                   # return simplified string by removing all the '0''s
    if lis=='':
        return lis
    for i,ele in enumerate(lis):
        if ele=='0':
            return sim(lis[:i]+lis[i+1:])
    return lis       

def simtup(tup):                 # simplify a tuple by removing '0''s of the tup[0]
    lis1=tup[0]                  # e.g. simtup(('30103','20002'))= ('313','202')
    lis2=tup[1]
    if lis1=='':
        return tup
    for i,ele in enumerate(lis1):
        if ele=='0':
            lis1=lis1[:i]+lis1[i+1:]
            lis2=lis2[:i]+lis2[i+1:]
            return simtup((lis1,lis2))
    return tup
                                    
def ediff(hx,x,n):                # d/dy=1/f' * d/dx.  for y=f(x)
    if n==0:
        return hx
    hhx=hx.diff(x)/f(x).diff(x)
    return ediff(hhx,x,n-1)

def ank(n,k):                    # the a^n_k in the note
    if (n,k) in ankdic:
        return ankdic[(n,k)]
    p1=0
    p2=0
    for i in range(1,k+2):
        p1=p1+Symbol('a_'+str(i))*x**i 
    for i in range(k+1):
        p2=p2+Symbol('b_'+str(i))*x**i 
    ff=(x**(n-1))*p2*(p1**(1-n))
    exp=ff.diff(x,k)/factorial(k)
    nu,de=fraction(together(exp))
    nu=series(nu,x,0,n=k+1)
    de=series(de,x,0,n=k+1)          
    temp=(nu/de).limit(x,0)
    for i in range (k+1):
        temp=temp.subs(Symbol('a_'+str(i+1)), ediff(x,x,i+1)/factorial(i+1))
        temp=temp.subs(Symbol('b_'+str(i)),ediff(f(x).diff(x),x,i)/factorial(i))
    ankdic[(n,k)]=simplify(temp)
    return ankdic[(n,k)]
    

def shd(exp):                    # replace all the derivatives by simpler notaion f^{(n)}
    for n in range(1,10):
        k=10-n
        dfx=f(x).diff(x,k)
        exp=exp.subs(dfx,Symbol('f^('+str(k)+')'))
    return expand(exp)

def simfunre(f,nn):
    lis=[x**n*re(N(f(x).diff(x,n).subs(x,0)))/factorial(n) for n in range(nn)]
    s=0
    for ele in lis:
        s+=ele
    return Lambda(x,s)
    
    
# functions for correlators     
    
    
class subset:                                #input a string. subset means all the str with weight lower than the input str
    def __init__(self,inputlis):
        self.lis=inputlis
        
    def dc(self):                           #return a dic, for str in subset, str: len(str)
        lis=self.lis
        l=len(lis)
        dic={}
        for n in range(l+1):
            dic[n]=[]
        for ele in sset(lis):
            q=sim(ele)
            ql=len(q)
            if q not in dic[ql]:
                dic[ql].append(q)
        return dic
    
    def ls(self):                      # return list of str in the subset
        lis=self.lis
        s=[]
        for ele in sset(lis):
            q=sim(ele)
            if q not in s:
                s.append(q)
        return s
    
    def ln(self):                       # return length of subset list 
        return len(self.ls())
    
    def basisls(self):
        bls=[]
        for ele in opedic:
            if ele[0]==self.lis:
                bls.append(ele[1])
        return bls
        
def simdic(dic):                          # merge OPE with the same operator content, '1203'~'123'
    tempdic={}
    for ele in dic:
        temp=sim(ele[1])
        temptup=(ele[0],temp)
        if temptup not in tempdic:
            tempdic[temptup]=dic[ele]
        else:
            tempdic[temptup]+=dic[ele]
    return tempdic

def findrule(tup1,tup2):               # return the permutation given tup1: the defaut order; tup2: the input order
    temp=[]
    lis2=list(tup2)
    for ele in tup1:
        ind=lis2.index(ele)
        temp.append(ind)
        lis2[ind]='none'
    return temp

def inds(n):                        #[(0,1)] in 2ops; [(0,1),(0,2),(1,2)] in 3ops
    nl=list(range(n))
    inds=[]
    for i in nl:
        for j in nl[i+1:]:
            inds.append((i,j))
    return inds

def phase(rule):                    # compansate the sign from the absolute value 
    n=len(rule)  
    s=0
    for ele in inds(n):
        a=-numpy.sign(rule[ele[0]]-rule[ele[1]])
        ex=hexp(rule[ele[0]],rule[ele[1]],n)
        s+=-int((1-a)/2)*ex
    return (-1)**s


def hexp(i,j,n):              # return h_i+h_j for n=2; h_3-h_1-h_2 for n=3,i=1,j=2...
    shl=0
    for ele in hl[:n]:
        shl+=ele
    if n==2:
        return -shl
    if n==3:
        return shl-2*hl[i]-2*hl[j]
    if n==4:
        return shl/3-hl[i]-hl[j]
        
       
                                   
def tris(*lis):                      
    return FrozenMultiset(lis)

def simp(exp,n,simple=True):           # first together, then simplify the numerator and denominator respectively
    ep1=exp.replace(lambda a: a.is_Pow and a.exp.is_Add, lambda a: a.subs([(ele,0) for ele in hl]))
    if simple==True:
        ep2=together(ep1)
        nu,de=fraction(ep2)
        nu=nu.subs([(var[ele[0]]-var[ele[1]],vardif[item]) for item,ele in enumerate(inds(n))])
        nu=nu.subs([(hexp(ele[0],ele[1],n),hhl[item]) for item,ele in enumerate(inds(n))])        
        # substitute (hl[2]-hl[0]-hl[1],hhl[0]),(hl[1]-hl[0]-hl[2],hhl[1]),(hl[0]-hl[1]-hl[2],hhl[2])
        # substitute (x-y,xd_1),(y-z,xd_2),(x-z,xd_3)
        de=de.subs([(var[ele[0]]-var[ele[1]],vardif[item]) for item,ele in enumerate(inds(n))])
        res=factor(nu)/factor(de)
        res=res.subs([(vardif[item],var[ele[0]]-var[ele[1]]) for item,ele in enumerate(inds(n))])
        res=res.subs([(hhl[item],hexp(ele[0],ele[1],n)) for item,ele in enumerate(inds(n))])
    else:
        res=ep1
    temp=[(var[ele[0]]-var[ele[1]])**hexp(ele[0],ele[1],n) for ele in inds(n)]
    temp=numpy.prod(temp)
    #xd1**(hhl[0])*xd2**(hhl[1])*xd3**(hhl[2])
    res=res*temp 
    return res
    



def reorder(st):      # L_{-1}L_{-2} --> L_{-2}L_{-1}+L_{-3}   reorder('12')={'21':1,'3':1}
    n=len(st)
    for i in range(n-1):
        if int(st[i])<int(st[i+1]):
            temp1=st[:i]+st[i+1]+st[i]+st[i+2:]
            temp2=str(int(st[i])+int(st[i+1]))
            temp3=int(st[i+1])-int(st[i])
            temp4=st[:i]+temp2+st[i+2:]
            return [(temp1,1),(temp4,temp3)]
    return((st,1))

def intpartition(n):    #intpartition(3)=['3','21','12','111']
    s=[]
    if n==0:
        return ['']
    for i in range(1,n+1):
        k=n-i+1
        for ele in intpartition(n-k):
            s.append(str(k)+ele)
    return s



def initialize():
    global CORdic
    CORdic={}
    for n in range(2,5):
        lis=['' for ele in range(n)]
        CORdic[tris(*lis)]=[numpy.prod([(var[ele[0]]-var[ele[1]])**hexp(ele[0],ele[1],n) for ele in inds(n)]), tuple(lis)]

        
def signature(g):
    la=lambda n: round(re(N(g(x).diff(x,n).subs(x,0))),3)
    return tuple(map(la,[0,1,2]))        
        
        
    
def write(value,triorder,tritup,createlist):
    triset=tris(*triorder)
    cordic[tritup]=value
    if createlist==1:
        directory[triset]=[triorder]
        os.mkdir('./cordata/'+str(triorder))
    else:
        directory[triset].append(tritup)
    with open('cordata/'+str(triorder)+'/'+str(tritup)+'.pkl','wb') as memory:
        pickle.dump(value,memory)  
    with open('directory.pkl','wb') as memory:
        pickle.dump(directory,memory)
    
def read(triorder,tritup):
    with open('cordata/'+str(triorder)+'/'+str(tritup)+'.pkl','rb') as memory:
        value=pickle.load(memory)
    cordic[tritup]=value
    return value
            
   
        
        
# the followings are objects





class OPE:                            # arguments are two strings of numbers e.g. OPE('233','012')
    def __init__(self,lis1='',lis2=''):        
        self.tup=(lis1,lis2)
        if self.tup in OPEdic:
            self.exist=1
            self.value=OPEdic[self.tup] 
        else:
            self.exist=0
            self.value=0
            
    def opeiter(self):                # calculate the OPE from smaller ones if doesn't exist
        tub=self.tup
        lis1=tub[0]
        lis2=tub[1]
        x1=int(lis1[0])
        x2=int(lis2[0])
        rlis1=lis1[1:]
        rlis2=lis2[1:]
        s1=strsum(rlis1)
        s2=strsum(rlis2)
        if (rlis1,rlis2) in OPEdic:
            v=OPEdic[(rlis1,rlis2)]
        else:
            return 'cannot compute'
        if lis1==lis2:
            return x1+v
        if x1==x2:
            return v
        if x1>x2>=1:
            if lis1[1:]==lis2[1:]:
                return 2*x1-x2+0*h
            else:
                return 0*h
        if x2==0:
            if lis1[1:]==lis2[1:]:
                return (2*x1+s1-s2)*v+c/12 *x1*(x1**2-1)
            else:
                return (2*x1+s1-s2)*v            

    def calculate(self):                    #use the method opeiter to calculate OPE and update value 
        if self.exist==1:
            return 'already exist'
        re=self.opeiter()
        if type(re)==str:
            return re
        self.value=re
        self.exist=1
        
    def record(self):                      #record the OPE value to OPEdic
        if self.exist==0:
            return 'not defined'
        if self.tup in OPEdic:
            return 'already exist'
        OPEdic[self.tup]=self.value
    
    

class expansion:                       # class of the full OPE expansion. argument is a single string 
    def __init__(self, lis):
        self.lis=lis
        
    def pri(self):                     # print the OPE equation
        if (self.lis,self.lis) not in OPEdic:
            return 'please update OPEdic first'
        exp=0
        tempdic={}
        s=sset(self.lis)
        for ele in s:
            tup=(self.lis,ele)
            temp=sim(ele)
            if temp not in tempdic:
                tempdic[temp]=0
            tempdic[temp]+=OPEdic[tup]
        for key in tempdic:
            exp+=simplify(tempdic[key])* z**(strsum(key)-strsum(self.lis)-2)*symbols('O^{('+key+')}',commutative=False)
        exp=exp.subs(Symbol('O^{()}',commutative=False),Symbol('O',commutative=False))
        equ=Symbol('TO^{('+self.lis+')}='+latex(exp))
        return equ    
    
    def update(self):                #used to generate the iteration computation of OPE data
        lis0=self.lis
        s1=sset(lis0)[1:]
        for ele in s1:
            lis1=sim(ele)  
            s2=sset(lis1)
            for lis2 in s2:
                p=OPE(lis1,lis2)
                p.calculate()
                p.record()
    
    
    
class trans:
    def __init__(self,lis1='',lis2=''):
        self.tup=(lis1,lis2)
        if self.tup in transdic:
            self.exist=1
            self.value=transdic[self.tup] 
        else:
            self.exist=0
            self.value=0
           
    def transiter(self):
        tup=self.tup
        lis1=tup[0]
        lis2=tup[1]
        n=int(lis1[0])
        m=int(lis2[0])
        slis1=lis1[1:]
        slis2=lis2[1:]
        if (slis1,slis2) not in transdic:
            return 'cannot compute'
        sls=slset(slis1,slis2)
        s=0
        if m==0:
            for ele in sls:
                if (slis1,ele) not in transdic:
                    return 'cannot compute'
                tupp=simtup((ele,slis2))
                if tupp not in OPEdic:
                    raise ValueError("OPEdic update")
                ope=OPEdic[tupp]
                s=s+ank(n,n+strsum(ele)-strsum(slis2))*transdic[(slis1,ele)]*ope
            if n>=2:
                s=s+c/12* 1/factorial(n-2)* sch.diff(x,n-2)* transdic[(slis1,slis2)]
        else:
            s=transdic[(slis1,slis2)]*ank(n,n-m)
        return s         
    
    def calculate(self):
        if self.exist==1:
            return 'already exist'
        res=self.transiter()
        if type(res)==str:
            return(res)
        res=simplify(res.subs(sch,schh))
        self.value=res
        self.exist=1

    def record(self):
        if self.exist==0:
            return 'not defined'
        if self.tup in transdic:
            return 'already exist'
        transdic[self.tup]=self.value 
        
        
        
class transform:
    def __init__(self, lis):
        self.lis=lis
    
    def pri(self):
        if (self.lis,self.lis) not in transdic:
            return 'please update transdic'
        exp=0
        tempdic={}
        s=sset(self.lis)
        for ele in s:
            tup=(self.lis,ele)
            temp=sim(ele)
            if temp not in tempdic:
                tempdic[temp]=0
            tempdic[temp]+=transdic[tup]
        for key in tempdic:
            exp+=shd(tempdic[key])*Symbol('O^{('+key+')}',commutative=False)
        exp=exp.subs(Symbol('O^{()}',commutative=False),Symbol('O',commutative=False))
        equ=Symbol('f_* O^{('+self.lis+')}='+latex(exp))
        return equ
    
    def trdic(self):
        dic={}
        for key in tradic:
            if key[0]==self.lis:
                dic[key]=tradic[key]
        return dic
    
    def update(self):
        lis0=self.lis
        s1=sset(lis0)[1:]
        for ele in s1:
            lis1=sim(ele)
            s2=sset(lis1)
            for lis2 in s2:
                p=trans(lis1,lis2)
                p.calculate()
                p.record()
    
    

class COR:                                               #class for correlation functions. input three strings
    def __init__(self,*inputtup):
        self.triset=FrozenMultiset(inputtup)     
        # use the unordered (but allow multiplicity) and unmutable (hashable) object to store in dic
        self.tritup=inputtup                     # use the ordered and unmutable object to keep the input order
        self.len=len(self.tritup)
        if self.triset in directory:
            self.exist=1
            self.trilis=directory[self.triset]
            self.triorder=self.trilis[0]
        else:
            self.exist=0
            self.triorder=self.orderset()  
            # reorder the list according to the levels. This is the default order of operators inside correlator
        
    def orderset(self):                                  # method to reorder the operator list, return unmutable tuple
        dic={}    
        for ele in self.triset:
            dic[ele]=subset(ele).ln()
        orderset=sorted(self.triset,key=dic.get,reverse=True)
        return tuple(orderset)
    
    def pri(self):
        # print the expression of correlator operators in the input order (in x,y,z ), based on the data stored in CORdic
        if self.exist==0:
            raise ValueError("please update CORdic") 
        if self.tritup in cordic:
            return cordic[self.tritup]
        if self.tritup in self.trilis:
            return read(self.triorder,self.tritup)
        else:
            if not self.triorder in cordic:
                read(self.triorder,self.triorder)
            value=self.caltup()
            write(value,self.triorder,self.tritup,0)
            return value        
        
    def caltup(self):          
        rule=findrule(self.triorder, self.tritup)             # convert the default order to input order using rule
        value=cordic[self.triorder]
        value=value.subs([(var[i], varsub[rule[i]]) for i in range(self.len) ])
        value=value.subs([(varsub[i],var[i]) for i in range(self.len)])
        value=value.subs([(hl[i],hhl[rule[i]]) for i in range(self.len)])
        value=value.subs([(hhl[i],hl[i]) for i in range(self.len)]) 
        ph=phase(rule)                                   # a phase correction due to the absolute value in the original cor
        return simp(value,self.len,simple=False)
                                                       
    
    def coriter(self):                            # method that implement the iteration equation, calculated in the default order 
        print('now computing'+str(self.triorder),  datetime.datetime.now().time())
        orderset=list(self.triorder)
        maxlis=orderset[0]                         # highest level operator  HLO (at the position 0 due to default order)
        m=int(maxlis[0])                           # the first vorosoro operator acting on HLO
        k=maxlis[1:]                               # the HLO with first vorosoro removed  HLOFR
        remain=orderset[1:]                        # the order two operators except HLO, denoted by remain  
        s=0                                        # store the output 
        for i,ele in enumerate(remain):            # a loop in the remain list 
            subele=subset(ele).basisls()
            templis=orderset.copy()
            templis[0]=k                           # new correlator list with the HLO replaced by  HLOFR
            yy=var[i+1]
            s+=-(yy-x)**(1-m)*COR(*templis).pri().diff(yy)   # the term involving derivatives in iteration 
            for els in subele:                     # loop in all the terms generated by OPE 
                d=strsum(ele)-strsum(els)
                templis[i+1]=els                   # new correlator list with remaining operators replaced by OPE generated ones 
                s+=(-1)**d* opedic[(ele,els)].subs(h,hl[i+1])*(yy-x)**(-m-d)*factorial(d+m-1)/factorial(d+1)/factorial(m-2)*COR(*templis).pri()
        return s                                   # unsimplified, in x,y,z coordinates.
    
    def calculate(self,record=1):                  # convert in more concise u and v, simplify the result, store in the dic
        if self.exist==1:
            return 'already exist'
        res=simp(self.coriter(),self.len)         # the only place to implement simplify, actually used together.
        self.exist=1
        if record==1:
            write(res,self.triorder,self.triorder,1)
        else:
            return res

        

        
#     def update(self):                         # calculate all the correlators at smaller levels 
#         if self.exist==1:
#             return 'already exist'
#         #print('im at'+str(self.triorder))
#         orderset=self.triorder
#         sub=subset(orderset[0]).ls()
#         for ele in sub[:-1]:
#             COR(ele,orderset[1],orderset[2]).update()
#         self.calculate()
#         self.record()    
        
            
class operator:
    def __init__(self,dim,level,xyz):
        self.dim=dim
        self.xyz=xyz
        if type(level)==str:
            self.codic={level:1}
            self.level=level
        else:
            self.codic=level
        self.fun=Lambda(x,x)
    
    def pri(self):
        s=0
        for ele,value in self.codic.items():
            s+=value*Symbol('O^'+'{('+ele+')}'+'_{h='+str(self.dim)+'}'+'('+str(self.xyz)+')')
        return s
    

    def trans(self,g):
        codic={}
        tup=(signature(g),self.dim,self.xyz)
        if tup in alltrdata:
            trdata=alltrdata[tup]
        else:
            trdata={}
            alltrdata[tup]=trdata
        for key,value in self.codic.items():
            p=transform(key)
            nu=simplify(abs(g(x).diff(x).subs(x,self.xyz))**self.dim)
            tempdic=p.trdic()
            for key2 in tempdic:               
                if key2 in trdata:
                    add=trdata[key2]
                else:
                    value2=tempdic[key2]
                    add=N(simplify(value2.subs([(c,0.5),(f,g),(h,self.dim),(x,self.xyz)])))
                    trdata[key2]=add
                add=nu*add
                if key2[1] in codic:
                    codic[key2[1]]+=value*add
                else:
                    codic[key2[1]]=value*add
        self.codic=codic
        self.fun=Lambda(x,g(self.fun(x)))
        self.xyz=N(g(self.xyz))
    

    
    
class descendants:
    def __init__(self,level):
        self.level=level
        self.states=self.allstate()
        self.basis,self.redic,self.redstate=self.statedicgen()
        self.innermatrix=[]
        self.norlis=[]

    def allstate(self):       #put states in all levels below n together
        n=self.level
        s=['']
        for k in range(1,n+1):
            s.extend(intpartition(k))
        return (s)

    def statedicgen(self):     
        #first return independent basis. Second return all the remaining state reordered as list
        n=self.level
        statedic={}
        states=self.states.copy()
        for ele in states:
            statedic[ele]=reorder(ele)
        basis=[]
        for ele in statedic:
            if type(statedic[ele])==tuple:
                basis.append(ele)
        for ele in basis:
            del statedic[ele]
            states.remove(ele)
        states.reverse()
        return basis,statedic,states

    def updatecor(self,num,cut=[]):    #update correlator, num is number of operators inserted. cut is optional cutoff  
        n=self.level
        #basis,red=statedicgen(n)
        if len(cut)==0:
            cut=[len(self.basis) for ele in range(num)]
        elif len(cut)!=num:
            raise ValueError("number in cut doesn't match num")
        if num==2:
            for ele1 in self.basis[:cut[0]]:
                for ele2 in self.basis[:cut[1]]:
                    p=COR(ele1,ele2)
                    p.calculate()
                    
        elif num==3:
            for ele1 in self.basis[:cut[0]]:
                for ele2 in self.basis[:cut[1]]:
                    for ele3 in self.basis[:cut[2]]:
                        p=COR(ele1,ele2,ele3)
                        p.calculate()
                        
        elif num==4:
            for ele1 in self.basis[:cut[0]]:
                for ele2 in self.basis[:cut[1]]:
                    for ele3 in self.basis[:cut[2]]:
                        for ele4 in self.basis[:cut[3]]:
                            p=COR(ele1,ele2,ele3,ele4)
                            p.calculate()
                            

    def condic(self,indic):    
        newdic=indic.copy() 
        for key in self.redstate:
            value=self.redic[key]
            for inkey in indic:
                if inkey[1]==key:
                    temp=newdic[inkey]
                    nk1=(inkey[0],value[0][0])
                    nu1=value[0][1]
                    nk2=(inkey[0],value[1][0])
                    nu2=value[1][1]
                    if nk1 in indic:
                        newdic[nk1]+=nu1*temp
                    else:
                        newdic[nk1]=nu1*temp
                    if nk2 in indic:
                        newdic[nk2]+=nu2*temp
                    else:
                        newdic[nk2]=nu2*temp
                    del newdic[inkey]
        return newdic
               
    def updateOPE(self):
        for ele in self.basis:
            p=expansion(ele)
            p.update()
        global opedic
        opedic=simdic(OPEdic)
        temp=list(opedic.keys()).copy()
        for key in temp:
            if key[0] not in self.basis:
                del opedic[key]
        update=1
        while update==1:
            opedic=self.condic(opedic)
            update=0
            for key in opedic:
                if key[1] in self.redstate:
                    update=1
                 
    def updatetrans(self):
        for ele in self.basis:
            print('now updating trans of', ele)
            p=transform(ele)
            p.update()
        global tradic
        tradic=simdic(transdic)
        temp=list(tradic.keys()).copy()
        for key in temp:
            if key[0] not in self.basis:
                del tradic[key]
        update=1
        while update==1:
            tradic=self.condic(tradic)
            update=0
            for key in tradic:
                if key[1] in self.redstate:
                    update=1
     
    def othbasis(self,level,dim):
        levelbasis=[ele for ele in self.basis if strsum(ele)==level]
        n=len(levelbasis)
        m=numpy.zeros((n,n))
        for i1,str1 in enumerate(levelbasis):
            for i2,str2 in enumerate(levelbasis):
                op1=operator(dim,str1,0)
                op2=operator(dim,str2,0)  
                op1.trans(Lambda(x,1/(x+1)))
                op2.trans(Lambda(x,x/(x+1)))
                print('computing',str1,str2)
                t=tensor(op1,op2)
                m[i1][i2]=t.value()
        print(m)
        self.innermatrix=m
        es,vs=linalg.eig(m)
        vs=vs.transpose()
        lis=[]
        for i in range(n):
            vr=vs[i].reshape(1,n)
            vc=vs[i].reshape(n,1)
            nx=vr.dot(m).dot(vc)[0][0]
            if nx>0.0000001:
                v=[ele/sympy.sqrt(nx) for ele in vs[i]]
                lis.append(v)
        norlis=[]
        for vec in lis:
            dic={}
            for i,ele in enumerate(levelbasis):
                dic[ele]=vec[i]
            norlis.append(dic.copy())
        self.norlis=norlis
        pnor=norlis.copy()
        for dic in pnor:
            for key,value in dic.copy().items():
                if value==0:
                    del dic[key]
        return pnor
                                                                          

        
        

class tensor:
    def __init__(self,*oplist):
        self.oplist=oplist
        self.ordlis=self.orderop()
        self.xyzlis=[ele.xyz for ele in self.ordlis]
        self.dimlis=[ele.dim for ele in self.ordlis]
        self.len=len(self.oplist)
        self.identity=tris(*[(self.dimlis[i],round(self.xyzlis[i],3)) for i in range(self.len)])
        if self.identity not in alltendic:
            alltendic[self.identity]={}
        self.tendic=alltendic[self.identity]
        
    def orderop(self):
        dic={}
        for ele in self.oplist:
            dic[ele]=ele.xyz
        return sorted(self.oplist,key=dic.get,reverse=True)
    
    def value(self):
        s=0
        if len(self.oplist)==2:
            for key1,value1 in self.ordlis[0].codic.items():
                for key2,value2 in self.ordlis[1].codic.items():
                    vv=COR(key1,key2).pri()
                    vv=vv.subs([(var[i],self.xyzlis[i]) for i in range(2)])
                    vv=vv.subs([(hl[i],self.dimlis[i]) for i in range(2)]).subs(hl[2],0)                 
                    vv=value1*value2*vv.subs(c,0.5)
                    s+=vv
            return s
        if len(self.oplist)==3:
            for key1,value1 in self.ordlis[0].codic.items():
                for key2,value2 in self.ordlis[1].codic.items():
                    for key3,value3 in self.ordlis[2].codic.items():
                        tup=(key1,key2,key3)
                        if tup in self.tendic:
                            vv=self.tendic[tup]
                        else:
                            vv=COR(key1,key2,key3).pri()
                            vv=vv.subs([(var[i],self.xyzlis[i]) for i in range(3)])
                            vv=vv.subs([(hl[i],self.dimlis[i]) for i in range(3)])
                            vv=vv.subs(c,0.5)
                            self.tendic[tup]=vv                         
                        vv=value1*value2*value3*vv
                        s+=vv
            return s
        if len(self.oplist)==4:
            for key1,value1 in self.ordlis[0].codic.items():
                for key2,value2 in self.ordlis[1].codic.items():
                    for key3,value3 in self.ordlis[2].codic.items():
                        for key4,value4 in self.ordlis[3].codic.items():
                            tup=(key1,key2,key3,key4)
                            if tup in self.tendic:
                                vv=self.tendic[tup]
                            else:
                                vv=COR(key1,key2,key3,key4).pri()
                                vv=vv.subs([(var[i],self.xyzlis[i]) for i in range(4)])
                                vv=vv.subs([(hl[i],self.dimlis[i]) for i in range(4)])
                                vv=vv.subs(c,0.5)
                                self.tendic[tup]=vv                         
                            vv=value1*value2*value3*value4*vv
                            s+=vv
            return s
    
        
    
    

