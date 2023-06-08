##################################################
#
# General Sakuma theorem: Case al=2bt, symmetric, lm<>bt
#
# (c) 2020 C. Franchi, M. Mainardis, S. Shpectorov
#
##################################################

# Field

bt:=Indeterminate(Rationals,"bt");;
lm:=Indeterminate(Rationals,"lm");;
lm2:=Indeterminate(Rationals,"lm2");;
F:=Field(bt,lm, lm2);;

al:=2*bt;;
lmf:=lm;;
lm2f:=lm2;;


# Field twist

gens:=GeneratorsOfField(F);;
bar:=c->Value(c,gens,[bt,lm,lm2]);;

# Visible algebra

n:=10;;
A:=F^n;;
a:=Basis(A);;
am2:=a[1];;
am1:=a[2];;
a0:=a[3];;
a1:=a[4];;
a2:=a[5];;
a3:=a[6];;
s1:=a[7];;
s2:=a[8];;
s2f:=a[9];;
s3:=a[10];;

names:=["am2","am1","a0","a1","a2","a3","s1","s2","s2f", "s3"];;

# Symmetries

tau0:=function(v)
 if v[6]<>Zero(F) then
  return fail;
 else
  return [v[5],v[4],v[3],v[2],v[1],v[6],v[7],v[8],v[9], v[10]];
 fi;
end;;

tau1:=function(v)
 if v[1]<>Zero(F) or v[10]<>Zero(F) then
  return fail;
 else 
  return [v[1],v[6],v[5],v[4],v[3],v[2],v[7],v[8],v[9], v[10]];  
 fi;
end;;

f:=function(v)
if v[10]<>Zero(F) then
 return fail;
 else
 return [bar(v[6]),bar(v[5]),bar(v[4]),bar(v[3]),bar(v[2]),
         bar(v[1]),bar(v[7]),bar(v[9]),bar(v[8]), bar(v[10])]; 
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

for i in [1..6] do
 Mult[i][i]:=a[i];
od;;
for i in [1..5] do
 Mult[i][i+1]:=s1+bt*(a[i]+a[i+1]);
od;;
Mult[1][3]:=s2+bt*(a[1]+a[3]);;
Mult[3][5]:=s2+bt*(a[3]+a[5]);;
Mult[2][4]:=s2f+bt*(a[2]+a[4]);;
Mult[4][6]:=s2f+bt*(a[4]+a[6]);;
Mult[3][6]:=s3+bt*(a0+a3);;

# Known products: a_i times sj

Mult[2][7]:=(al-bt)*s1+(lmf*(1-al)+bt*(al-bt-1))*a[2]+
  (1/2)*(al-bt)*bt*(a[1]+a[3]);;
Mult[3][7]:=(al-bt)*s1+(lm*(1-al)+bt*(al-bt-1))*a[3]+
  (1/2)*(al-bt)*bt*(a[2]+a[4]);;
Mult[4][7]:=(al-bt)*s1+(lmf*(1-al)+bt*(al-bt-1))*a[4]+
  (1/2)*(al-bt)*bt*(a[3]+a[5]);;
Mult[5][7]:=(al-bt)*s1+(lm*(1-al)+bt*(al-bt-1))*a[5]+
  (1/2)*(al-bt)*bt*(a[4]+a[6]);;
Mult[3][8]:=(al-bt)*s2+(lm2*(1-al)+bt*(al-bt-1))*a[3]+
  (1/2)*(al-bt)*bt*(a[1]+a[5]);;
Mult[4][9]:=(al-bt)*s2f+(lm2f*(1-al)+bt*(al-bt-1))*a[4]+
  (1/2)*(al-bt)*bt*(a[2]+a[6]);;
  
  
# Projection onto a0

lambda:=function(u)
 if u[6]=Zero(F) and u[9]=Zero(F) and u[10]=Zero(F) then 
  return u*[lm2,lm,One(F),lm,lm2,Zero(F),lm-bt-bt*lm,
         lm2-bt-bt*lm2,Zero(F), Zero(F)]; 
 else 
  return fail; 
 fi;
end;;

Print("Basics done\n");;

#
# Eigenvectors
#

v1:=(s1+(bt-lm)*a0+(bt/2)*(a1+am1))/al;;
u1:=a1-lm*a0-v1-(a1-am1)/2;;

uu:=Times(u1,u1);;
uv:=Times(u1,v1);;
vv:=Times(v1,v1);;

#
# Additional values of lambda
#

# uu+uv has zero projection, no s1s1, no a3, and 
# s2f/4

ls2f:=-4*lambda(uu[1]+uv[1]-s2f/4);;

# Now update lambda

lambda:=function(u)
 if u[6]=Zero(F) and u[10]=Zero(F) then 
  return u*[lm2,lm,One(F),lm,lm2,Zero(F),lm-bt-bt*lm,
         lm2-bt-bt*lm2, ls2f, Zero(F)]; 
 else 
  return fail; 
 fi;
end;;

# uu has zero projection, no a3, and s1*s1/(4*bt^2)

ls1s1:=-4*(bt^2)*lambda(uu[1]);;

#
# Express s2 and s2f
#

w:=uu[1]-vv[1];;
w:=w-lambda(w)*a0;;

# w must be a 0-eigenvector, hence we get a relation

r:=Times(a0,w);;

# r involves s2 with coefficient -bt/2

S2:=2*r/bt+s2;;
S2f:=f(S2);;

# Function update

update:=function(v)
  return v-v[8]*s2+v[8]*S2-v[9]*s2f+v[9]*S2f;
  end;;



#
# define Mult[3][9] and update Mult[3][8]
Mult[3][9]:=update(Times(a0, S2f));;
Mult[9][3]:=Mult[3][9];;
Mult[3][8]:=update(Times(a0, S2));;
Mult[8][3]:=Mult[3][8];;
Mult[2][4]:=update(Mult[2][4]);;

#
# Express a4 and am3
#

# tau1(S2)-S2=0 and this contains -bt*a4/2

A4:=update(2*(tau1(S2+(bt/2)*am2)-S2)/bt);;
Am3:=update(f(A4));;


# Update tau0 and tau1

tau0:=function(v)
 return [v[5],v[4],v[3],v[2],v[1],Zero(F),v[7],Zero(F),Zero(F), v[10]]
        +v[6]*Am3+v[8]*S2+v[9]*S2f;
end;;

tau1:=function(v)
 if v[10]<>Zero(F) then
 return fail;
 else
 return [Zero(F),v[6],v[5],v[4],v[3],v[2],v[7],Zero(F),Zero(F), Zero(F)]
        +v[1]*A4+v[8]*S2+v[9]*S2f; 
        fi;
end;;
# 

# Add products with s1

Mult[1][7]:=(al-bt)*s1+(lm*(1-al)+bt*(al-bt-1))*a[1]+
  (1/2)*(al-bt)*bt*(Am3+a[2]);;
 Mult[7][1]:=Mult[1][7];;  
Mult[6][7]:=(al-bt)*s1+(lmf*(1-al)+bt*(al-bt-1))*a[6]+
  (1/2)*(al-bt)*bt*(a[5]+A4);;
 Mult[7][6]:=Mult[6][7];;
  Mult[5][7]:=(al-bt)*s1+(lm*(1-al)+bt*(al-bt-1))*a[5]+
  (1/2)*(al-bt)*bt*(a[4]+a[6]);;
Mult[7][5]:=Mult[5][7];;
#
# Find lm3 
#

# w is a 0-eigenvector involving only am2...a2 and s1
# we use u_1 to get rid of s1

z:=w+2*(-2*bt+lm)*u1;;

# this can be multiplied with s1 and the result has 
# lambda equal zero

zs:=Times(z,s1);;

# a3 appears with coefficient -(bt^3)/4

lm3:=4*lambda(zs+((bt^3)*a3)/4)/(bt^3);;

# update lambda

lambda:=function(u)
 return u*[lm2,lm,One(F),lm,lm2,lm3,lm-bt-bt*lm,
         lm2-bt-bt*lm2, ls2f,  lm3-bt-bt*lm3];
end;;

# Find s1*s1: a0*(uu+uv)=al*(uv[1]-(1/(4*bt^2))*s1*s1 )

s1s1:=4*bt^2*(uv[1]-Times(a0, uu[1]+uv[1])/al);;
s1s1:=update(s1s1);;
Mult[7][7]:=s1s1;;

# s1*s1 has the coefficient of s3 equal to (1/4)*bt^2. 
# s1*s1-f(s1*s1) contains s3f with coefficient -(1/4)*bt^2

s3f:=(s1s1-f(s1s1-s1s1[10]*s3))/s1s1[10];;
s3t:=tau0(s3f);;

# update f and tau1

f:=function(v)
 return [bar(v[6]),bar(v[5]),bar(v[4]),bar(v[3]),bar(v[2]),
         bar(v[1]),bar(v[7]),bar(v[9]),bar(v[8]), Zero(F)]+bar(v[10])*s3f; 
end;;

tau1:=function(v)
 return [Zero(F),v[6],v[5],v[4],v[3],v[2],v[7],v[8],v[9], Zero(F)]
        +v[1]*A4+v[10]*s3t; 
end;;

Print("lambda, tau0, tau1 are complete\n");;

# relations d1, d2, D1, D2, 

d1:=f(s3t)-s3t;;     
d2:=tau1(d1);;       

D1:=tau0(d1)-d1;;  
D2:=tau0(d2)-d2;;


poly1:=lambda(d1);; 
poly2:=lambda(d2);;

# 
# Complete the multiplication table
#
Mult[1][4]:=s3f+bt*(am2+a1);; Mult[4][1]:=Mult[1][4];;
Mult[2][5]:=s3t+bt*(am1+a2);; Mult[5][2]:=Mult[2][5];;
Mult[2][6]:=tau0(update(Times(a1,Am3)));;  Mult[6][2]:=Mult[2][6];;
Mult[1][5]:=f(Mult[2][6]);; Mult[5][1]:=Mult[1][5];;
Mult[1][6]:=tau0(Times(Am3,a2));; Mult[6][1]:=Mult[1][6];;
Mult[1][8]:=update(Times(am2, S2));; Mult[8][1]:=Mult[1][8];;
Mult[1][9]:=update(Times(am2, S2f));;
Mult[8][1]:=Mult[1][8];;


Mult[3][10]:=(al-bt)*s3+(lm3*(1-al)+bt*(al-bt-1))*a0+
  (1/2)*(al-bt)*bt*(Am3+a3);;  Mult[10][3]:=Mult[3][10];;
Mult[4][10]:=f(update(Times(a0, s3f)));;   Mult[10][4]:=Mult[4][10];;
Mult[5][10]:=tau1(update(Times(a0, s3t)));;  Mult[10][5]:=Mult[5][10];;
Mult[1][10]:=tau0(Mult[5][10]);;  Mult[10][1]:=Mult[1][10];;
Mult[2][10]:=tau0(Mult[4][10]);;  Mult[10][2]:=Mult[2][10];;
Mult[6][10]:=f(update(Times(am2, s3f)));;  Mult[10][6]:=Mult[6][10];;

Mult[6][8]:=update(Times(a3, S2));;  Mult[8][6]:=Mult[6][8];;
Mult[6][9]:=update(Times(a3, S2f));; Mult[9][6]:=Mult[6][9];;

# Find s3*s3

u3:=-s3+(lm3-al*lm3-bt)*a0+((al-bt)/2)*(a3+Am3);;  
v3:=s3+(bt-lm3)*a0+bt*(a3+Am3)/2;;   
u3u3:=Times(u3, u3);; 
u3v3:=Times(u3, v3);; 
v3v3:=Times(v3, v3);; 

# u3v3 is an al-eigenvector and contains s3*s3 with coefficient -1
ls3s3:=lambda(u3v3[1]);;

# phi3 is a 0-eigenvector for a0
phi3:=u3u3[1]-v3v3[1]- (lambda(u3u3[1]-v3v3[1]))*a0;;

psi3:=u3u3[1]+u3v3[1];;

s3s3:=(-Times(a0, psi3)+al*u3v3[1])/al;;

Mult[10][10]:=update(s3s3);;


u1u3:=Times(u1, u3);; # contains  s1*s3 with coefficient 1/(2*bt)
u1v3:=Times(u1, v3);; #contains  s1*s3 with coefficient -1/(2*bt)
C:=u1u3[1]+u1v3[1];;

s1s3:=2*bt*(u1v3[1]-Times(a0, C)/al);;
Mult[7][10]:=update(s1s3);; Mult[10][7]:=Mult[7][10];;

Print("Multiplication table is complete\n");;

   
# Function lambdb
#   
lambdb:=function(u)  
 return(bar(lambda(f(u))));
end;;

# More relations
#
id3:=Times(Am3,Am3)[1]-Am3;;
poly3:=lambda(id3);; 
id4:=Times(A4,A4)-A4;;
poly4:=lambda(id4);;  

e:=update(Times(tau1(u1), tau1(v3)));;
ee:=update(Times(a2, e)-2*bt*e);;

# 
# Since we are assuming lm<>bt, from relation D1 we express am2
#D1 must be zero and contains am2 with non zero coefficinet
#
Am2:=-(D1-D1[1]*am2)/D1[1];;
A3:=f(Am2);;

update1:=function (u)
return( u-u[1]*am2+u[1]*Am2-u[6]*a3+u[6]*A3);
end;;

S3:=update1(update(Times(a0, A3)-bt*(a0+A3)));;

update2:=function (u)
uu:=update1(u);
return( uu-uu[10]*s3+uu[10]*S3);
end;;

#
# d1 becomes
dd1:=update2(d1);;
b:=update2(d1)[2];;
c:=update2(d1)[3];;

# 
# Now we assign all possible values to (lm, lm2) 
#
# define the valuation functions for coefficients and vectors
val:=function (B, l, l2, p)
return(Value(p,gens,[B, l, l2]));
end;

Val:=function (B, l, l2, u)
return([val(B, l, l2, u[1]), val(B, l, l2, u[2]),val(B, l, l2, u[3]),val(B, l, l2,u[4]),val(B, l, l2, u[5]),val(B, l, l2, u[6]),val(B, l, l2, u[7]),val(B, l, l2, u[8]),val(B, l, l2, u[9]), val(B, l, l2, u[10])]);
end;;


#
# Case lm=lm2=(9*bt^2-2*bt)/(8*bt-2). 
#
# Am2 and A3  are idempotents


eq1:=Val(bt, (9*bt^2-2*bt)/(8*bt-2), (9*bt^2-2*bt)/(8*bt-2), mu, update2(update(Times(Am2, Am2)-Am2)));

eq2:=Val(bt, (9*bt^2-2*bt)/(8*bt-2), (9*bt^2-2*bt)/(8*bt-2),mu, update2(update(Times(A3, A3)-A3)));

# from equations eq1=0 and eq2=0 we get a2=am1 
#
update3:=function (u)
uu:=update2(u);
return( uu-uu[2]*am1+uu[2]*a2);
end;; 

# check the multiplication table
M:=List([[3,4], [3,5], [3,7], [4,5], [4,7], [5,7], [7,7]], x->Val(bt, (9*bt^2-2*bt)/(8*bt-2), (9*bt^2-2*bt)/(8*bt-2), update3(update(Mult[x[1]][ x[2]]))));


#
# Case lm=lm2=bt/2. 
#
# we evaluate coefficients b and c in relation d1=0.
val(bt, bt/2, bt/2, b);
val(bt, bt/2, bt/2, c);

#Am2 is an idempotent

eq1:=Val(bt, bt/2, bt/2, update2(update(Times(Am2, Am2)-Am2)));

# we see at the expression for S2
Val(bt, bt/2, bt/2, update2(S2));
# if b<>0 and the coefficient of a2 in eq1 is non zero, then am1=2, then s1=S2 and from the above expression we need to consider the cases: bt<>1/5 and bt=1/5. If bt=1/5, then bt/2=(9*bt^2-2*bt)/(8*bt-2) and we are in the previous case. 
# If bt<>1/5, then we may express s1=-bt/2*(a0+a1+a2)

# Assume b=0 and the coefficient of a2 in eq1 is zero: then F has characteristic 7 and bt=2, 2*bt=4=1/2 and lm=lm2=bt/2=1
#
# Am2 becomes Am2=a2+a0-am1: we get the algebra 6Y(1/2,2) with q=s1+a0+a1+4am1+4a2
# check the multiplication table
#M:=List([ [2,3], [2,4], [2,5], [2,7], [3,4], [3,5], [3,7], [4,5], [4,7], [5,7], [7,7]], x->Val(1, 1, 1,update2(update(Mult[x[1]][ x[2]]))));

# 
# Case lm=0, lm2=1. 
#
# we evaluate coefficients b and c in relation d1=0.
val(bt, 0, 1, b);
val(bt, 0, 1, c);

# we evaluate relation D2=0
Val(bt, 0,1, update2(D2)); # -2*(2*bt-1)*val(bt, 0,1,b)/bt*(am1-a1)

# we evaluate relation A3^2-A3=0
Val(bt, 0,1, update2(update(Times(A3, A3)-A3)));
# [ 0, (-720*bt^4+320*bt^3+360*bt^2-250*bt+40)/(bt^3-2*bt^2+bt), 
#  (-180*bt^4-180*bt^3+375*bt^2-160*bt+20)/(bt^3-2*bt^2+bt), 
#  -(-720*bt^4+320*bt^3+360*bt^2-250*bt+40)/(bt^3-2*bt^2+bt), 
#  -(-180*bt^4-180*bt^3+375*bt^2-160*bt+20)/(bt^3-2*bt^2+bt), 0, 0, 0, 0, 
#  0 ]

# we evaluate relation ee=0 and ee-tau0(ee)=0  
Val(bt, 0,1, update2(ee)); 
Val(bt, 0,1, update2(ee-tau0(ee)));   

# 
# Case lm=lm2=1
#
# we evaluate relation D2=0
Val(bt, 1,1,mu, update2(D2));

# we evaluate coefficients b and c in relation d1=0.
val(bt, 1, 1, b); #(-36*bt^4+126*bt^3-127*bt^2+48*bt-6)/(bt^3)
val(bt, 1, 1, c); #(-36*bt^5+94*bt^4-23*bt^3-56*bt^2+30*bt-4)/(bt^4)

# 
# Case lm=mu, lm2=1
#
# we evaluate expressions Am2 and A3
Val(1/4, lm,1, update2(D2));
Val(1/4, lm,1, update2(Am2));
Val(1/4, lm, 1,  update2(A3));

Val(1/4, lm,1, update2(D1));
Val(1/4, lm,1, update2(e));
Val(1/4, lm,1, update2(ee-tau0(ee)));


# 
# Case lm=(18*bt^2-bt-2)/(2(8*bt-3)),  lm2=(48*bt^4-28*bt^3+7*bt-2)*(3*bt-1)/(2*bt^2*(8*bt-3)^2)

Lm:=(18*bt^2-bt-2)/(2*(8*bt-3));
Lm2:=(48*bt^4-28*bt^3+7*bt-2)*(3*bt-1)/(2*bt^2*(8*bt-3)^2);

val(bt, Lm, Lm2, b); #(-36*bt^4+126*bt^3-127*bt^2+48*bt-6)/(bt^3)
val(bt, Lm, Lm2, c); #
Val(bt, Lm,Lm2, update2(D2));

# if 4*bt^2+2*bt-1=0 we get lm=bt+1/4 and lm2=bt
Lm:=bt+1/4;
Lm2:=bt;
Val(bt, Lm,Lm2, update2(ee)); #0
Val(bt, Lm,Lm2, update2(A3)); #[ 0, 1, (-2*bt^2-bt+1/2)/(-2*bt^3+2*bt^2), 0, 
  (1/2*bt^2+1/4*bt-1/8)/(-1/2*bt^3+1/2*bt^2), 0, 0, 0, 0, 0 ]=am1
  
# if bt=2/7
Lm:=(18*bt^2-bt-2)/(2*(8*bt-3));
Lm2:=(48*bt^4-28*bt^3+7*bt-2)*(3*bt-1)/(2*bt^2*(8*bt-3)^2);
val(2/7, Lm, Lm2, Lm);  #4/7
val(2/7, Lm, Lm2, Lm2);  # 4/7
val(2/7, Lm, Lm2, (9*bt^2-2*bt)/(8*bt-2)); #4/7

