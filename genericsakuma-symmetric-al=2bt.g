##################################################
#
# General Sakuma theorem: Symmetric case al=2bt
#
# (c) 2020 C. Franchi, M. Mainardis, S. Shpectorov
#
##################################################

# Field

bt:=Indeterminate(Rationals,"bt");;
lm2:=Indeterminate(Rationals,"lm2");;
lm4:=Indeterminate(Rationals,"lm4");;
F:=Field(bt,lm2,lm4);;

al:=2*bt;

# Visible algebra

n:=8;;
A:=F^n;;
a:=Basis(A);;
am4:=a[1];;
am2:=a[2];;
a0:=a[3];;
a2:=a[4];;
a4:=a[5];;
s2:=a[6];;
s4:=a[7];;
s4t:=a[8];;

names:=["am4","am2","a0","a2","a4","s2","s4","s4t"];;

# Symmetries

tau0:=function(v)
 return [v[5],v[4],v[3],v[2],v[1],v[6],v[7],v[8]];
end;;

tau1:=function(v)
 if v[1]<>Zero(F)  then 
  return fail; 
 else 
  return [v[1],v[5],v[4],v[3],v[2],v[6],v[8],v[7]]; 
 fi;
end;;


#
# Algebra multiplication
#

Mult:=List([1..n],i->[]);;

# Product function

Times:=function(u,v)
 local ans,rem,i,j,m;
 ans:=Zero(F)*a[1];
 rem:=[];
 for i in [1..n] do
  m:=u[i]*v[i];
  if m<>Zero(F) then
   if IsBound(Mult[i][i]) then
    ans:=ans+m*Mult[i][i];
   else
    Add(rem,[[i,i],m]);
   fi;
  fi;
  for j in [i+1..n] do
   m:=u[i]*v[j]+u[j]*v[i];
   if m<>Zero(F) then
    if IsBound(Mult[i][j]) then
     ans:=ans+m*Mult[i][j];
    else
     Add(rem,[[i,j],m]);
    fi;
   fi;
  od;
 od;
 if rem=[] then 
  return ans;
 else
  return [ans,rem];
 fi;
end;;

# Display the unknown products

DisplayRem:=function(rem)
 local i;
 for i in [1..Length(rem)] do
  if i>1 then
   Print("+");
  fi;
  Print("(",rem[i][2],")*",names[rem[i][1][1]],"*",
                           names[rem[i][1][2]]);
 od;
 Print("\n");
end;;

# Known products: ai times aj

for i in [1..5] do
 Mult[i][i]:=a[i];
od;;
for i in [1..4] do
 Mult[i][i+1]:=s2+bt*(a[i]+a[i+1]);
od;;
Mult[1][3]:=s4+bt*(a[1]+a[3]);;
Mult[3][5]:=s4+bt*(a[3]+a[5]);;
Mult[2][4]:=s4t+bt*(a[2]+a[4]);;

# Known products: a_i times sj

Mult[2][6]:=(al-bt)*s2+(lm2*(1-al)+bt*(al-bt-1))*a[2]+
  (1/2)*(al-bt)*bt*(a[1]+a[3]);;
Mult[3][6]:=(al-bt)*s2+(lm2*(1-al)+bt*(al-bt-1))*a[3]+
  (1/2)*(al-bt)*bt*(a[2]+a[4]);;
Mult[4][6]:=(al-bt)*s2+(lm2*(1-al)+bt*(al-bt-1))*a[4]+
  (1/2)*(al-bt)*bt*(a[3]+a[5]);;
Mult[3][7]:=(al-bt)*s4+(lm4*(1-al)+bt*(al-bt-1))*a[3]+
  (1/2)*(al-bt)*bt*(a[1]+a[5]);;

  
# Projection onto a0

lambda:=function(u)
 if u[8]=Zero(F) then 
  return u*[lm4,lm2,One(F),lm2,lm4,lm2-bt-bt*lm2,
         lm4-bt-bt*lm4,Zero(F)]; 
 else 
  return fail; 
 fi;
end;;

Print("Basics done\n");;

#
# Eigenvectors
#

v2:=(s2+(bt-lm2)*a0+(bt/2)*(a2+am2))/al;;
u2:=a2-lm2*a0-v2-(a2-am2)/2;;

u2u2:=Times(u2,u2);;
u2v2:=Times(u2,v2);;
v2v2:=Times(v2,v2);;


#
# The additional values of lambda
#

# u2u2+u2v2 has zero projection, no s2s2, and 
# s4t times 1/4

ls4t:=-4*lambda(u2u2[1]+u2v2[1]-s4t/4);;

# Now update lambda

lambda:=function(u)
 return u*[lm4,lm2,One(F),lm2,lm4,lm2-bt-bt*lm2,
         lm4-bt-bt*lm4,ls4t]; 
end;;

# u2u2 has zero projection and s2*s2/(4*bt^2)

ls2s2:=-(4*bt^2)*lambda(u2u2[1]);;

#
# Express a0*s4t
#

T0:=u2u2[1]-v2v2[1];;
T:=T0-lambda(T0)*a0;;

# T must be a 0-eigenvector, hence we get a relation

r:=Times(a0,T);;

# r involves s4 with coefficient -bt/2

S4:=(r+(1/2)*bt*s4)*(2/bt);;

# r contains am4 with coefficient -(1/4)*bt^2. By applying tau1 we obtain a6

A6:=tau1(r+(1/4)*bt^2*am4)*(4/(bt^2));; 

#
# Now update tau1
#

 tau1:=function(v)
  return A6*v[1]+[0,v[5],v[4],v[3],v[2],v[6],v[8],v[7]]; 
end;;

Print("lambda, tau0, tau1 are complete\n");;

#
# Define new products 
#

Mult[4][8]:=tau1(Times(a0,s4));;
Mult[2][8]:=tau0(Mult[4][8]);;
Mult[5][7]:=tau1(Mult[2][8]);;
Mult[1][7]:=tau0(Mult[5][7]);;

# eigenvectors 

v4:=(s4+(bt-lm4)*a0+(bt/2)*(a4+am4))/al;;
u4:=a4-lm4*a0-v4-(a4-am4)/2;;

u4u4:=Times(u4,u4);;
u4v4:=Times(u4,v4);;
v4v4:=Times(v4,v4);;

# Express a0*s4t

T04:=u4u4[1]-v4v4[1];;

#
# u4u4 has projection 0 and contains 1/(4*bt^2)*s4*s4 and (1/8)* am4*a4 
# v4v4 contains 1/(4*bt^2)*s4*s4 and (1/8)* am4*a4 
#
L:=-lambda(u4u4[1]);; 
T4:=T04+(lambda(v4v4[1])+L)*a0;; 
# T4 is a 0-eigenvector for a0
#
a0s4t:=-Times(a0, T4)[1]/(Times(a0, T4)[2][1][2]);;
#
# relation if Times(a0, T4)[2][1][2]=0, i.e. (4*bt-1)*(lm2-bt)=0
#









# Assume (4*bt-1)*(lm2-bt)=0, i.e. lm2=bt
#
lm2:=bt;;

r2:=-Times(a0, T4)[1];;  # gives the same relation as r=0


 Times(A6, A6);; # equal to Times(A6, A6)[1]+(4/(bt^2))*s4t*s4t
 # from identity a6^2=a6 we deduce s4t*s4t
#
Mult[8][8]:=(bt^2)*(A6-Times(A6,A6)[1])/4;; 
Mult[7][7]:=tau1(Mult[8][8]);;
#
#
r3:=Mult[8][8]-tau0(Mult[8][8]);;  

#  if lm4<>bt/2, r3=0 implies a2=am2 => a4=am4=a0

ss4:=(1-2*bt)*a0;;
ss4t:=(1-2*bt)*a2;;
a0ss4t:=(1-2*bt)*Times(a0, a2);;
#
# deduce s2*s2
#
Q:=u2u2[1]+u2v2[1];;
#Times(a0, Q)=Times(a0, Q)[1]+1/4*a0*s4t
#
a0Q:=Times(a0, Q)[1]+(1/4)*a0ss4t;;

s2s2:=-4*bt^2*a0Q/al+4*bt^2*u2v2[1];;
# we get an algebra of dimension 3 (equal to the subalgebra <<d1,d6>> in Vijay 
#  algebra of dimension 8 with u=-(1/bt)*s2

#
#
# Case lm4=bt/2: we find bt=1, a contradiction
#
lm4:=bt/2;
#
#
Q4:=Times(u4,u4)[1]+Times(u4, v4)[1];;
#
mult15:=8*Times(a0, Q4)[1]/al-8*Times(u4,v4)[1];;
Mult[1][5]:=mult15-(1/bt)*s4+(1/bt)*S4;;

#
#Times(am2, A6) has a0*s4t with coefficient 0
#
r4:=Times(am2, A6)[1]-tau1(Mult[1][5]);; # [ 0, 0, 0, 1/2*bt-1/2, 0, 0, 0, 0 ]



 


