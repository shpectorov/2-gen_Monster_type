//
// Generic Sakuma theorem: Majorana case
//
// (c) 2020 C. Franchi, M. Mainardis, S. Shpectorov
//
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
LIB "solve.lib";
ring F=(0),( lm, lmf, lm2, lm2f), dp;
poly al=1/4;
poly bt=1/32;
freemodule(8);
vector am2=gen(1);
vector am1=gen(2);
vector a0=gen(3);
vector a1=gen(4);
vector a2=gen(5);
vector s1=gen(6);
vector s2=gen(7);
vector s2f=gen(8);
list a=am2,am1,a0,a1,a2,s1,s2,s2f;
list r=0,0,0,0,0,0,0,0;
list Mult=r,r,r,r,r,r,r,r;

Mult[1][1]=am2; Mult[2][2]=am1; Mult[3][3]=a0; Mult[4][4]=a1; Mult[5][5]=a2; 

vector m12=s1+bt*(a[1]+a[2]);
vector m23=s1+bt*(a[2]+a[3]);
vector m34=s1+bt*(a[3]+a[4]);
vector m45=s1+bt*(a[4]+a[5]);
vector m13=s2+bt*(a[1]+a[3]);
vector m35=s2+bt*(a[3]+a[5]);
vector m24=s2f+bt*(a[2]+a[4]);

Mult[1][2]= m12; Mult[2][1]=m12;  Mult[1][3]= m13; Mult[3][1]=m13; Mult[2][3]= m23; Mult[3][2]=m23;  Mult[3][4]= m34; Mult[4][3]=m34;  Mult[4][5]= m45; Mult[5][4]=m45;  Mult[3][5]= m35; Mult[5][3]=m35;    Mult[2][4]= m24; Mult[4][2]=m24;  

vector m26=(al-bt)*a[6]+(lmf*(1-al)+bt*(al-bt-1))*a[2]+
  (1/2)*(al-bt)*bt*(a[1]+a[3]);
vector m36=(al-bt)*a[6]+(lm*(1-al)+bt*(al-bt-1))*a[3]+
  (1/2)*(al-bt)*bt*(a[2]+a[4]);
vector m46=(al-bt)*a[6]+(lmf*(1-al)+bt*(al-bt-1))*a[4]+
  (1/2)*(al-bt)*bt*(a[3]+a[5]);
vector m37=(al-bt)*a[7]+(lm2*(1-al)+bt*(al-bt-1))*a[3]+
  (1/2)*(al-bt)*bt*(a[1]+a[5]);
  
Mult[2][6]= m26; Mult[6][2]=m26; Mult[3][6]= m36; Mult[6][3]=m36;  Mult[4][6]= m46; Mult[6][4]=m46; Mult[3][7]= m37; Mult[7][3]=m37; 
 
proc Times (vector u, vector v)
{
vector ans=[0];
list rem=list();
 for(int i=1; i<=8; i=i+1)
  { if (u[i]<>0)
     {
        for(int j=1; j<=8; j=j+1)
          {
              if (v[j]<>0)
               { if (Mult[i][j]<>0*a[1])
                   {
                   ans=ans+u[i]*v[j]*Mult[i][j];
                   }
                   else
                  { list l=list(i,j), u[i]*v[j];
                      rem=rem+l;
                   }             
          }  
     }
  }
  }
    if (size(rem)==0)
       {   return(ans);
           }
   else
       {list k=ans, rem;
      return(k);}
}

// Symmetries

proc tau0 (vector v)
  {
    return(v[5]*a[1]+v[4]*a[2]+v[3]*a[3]+v[2]*a[4]+v[1]*a[5]+v[6]*a[6]+v[7]*a[7]+v[8]*a[8]);        
  }  
 
map ff=F, lmf,lm, lm2f, lm2;

proc fold (vector v)
{
poly v1=v[1];
poly v2=v[2];
poly v3=v[3];
poly v4=v[4];
poly v5=v[5];
poly v6=v[6];
poly v7=v[7];
poly v8=v[8];
poly ffv2=ff(v2); 
poly ffv3=ff(v3);
poly ffv4= ff(v4); 
poly ffv5=ff(v5); 
poly ffv6=ff(v6); 
poly ffv7=ff(v7); 
poly ffv8=ff(v8);

if (v1==0)
       {vector s=ffv5*a[2]+ffv4*a[3]+ffv3*a[4]+ffv2*a[5]+ffv6*a[6]+ffv8*a[7]+ffv7*a[8];
        return(s);}
        else
          {return("fail");}
          } 
          
proc lambda (vector v)
{
 if (v[8]==0) 
  { poly p= lm2*v[1]+lm*v[2]+v[3]+lm*v[4]+lm2*v[5]+(lm-bt-bt*lm)*v[6]+(lm2-bt-bt*lm2)*v[7];
  return(p); }
else
          {return("fail");}
}        
 
vector v1= (s1+(bt-lm)*a0+(bt/2)*(a1+am1))/al; // 
vector u1=a1-lm*a0-v1-(a1-am1)/2;  // 

vector uu=Times(u1, u1)[1];  
vector uv=Times(u1, v1)[1]; 
vector vv=Times(v1, v1)[1]; 

// (uu+uv) is a 0-eigenvector for a0 and contains s2f: we compute lambda(s2f)

vector w=(uu+uv)-(uu+uv)[8]*s2f;
 
poly ls2f=-lambda(w)/((uu+uv)[8]);

// update lambda

proc lambda (vector v)
{
   poly p= lm2*v[1]+lm*v[2]+v[3]+lm*v[4]+lm2*v[5]+(lm-bt-bt*lm)*v[6]+(lm2-bt-bt*lm2)*v[7]+ls2f*v[8];
  return(p); 
  } 
  
// u1*u1 is a 0-eigenvector for a0, hence it has 0-projection on a0, and it contains 1/(al^2)*s1*s1 

poly ls1s1=-(al^2)*lambda(uu);; // lambda(s1*s1)

//
// Express a0*s2f
//
vector w=uu-vv -lambda(uu-vv)*a0; // this is a 0-eigenvector for a0
// Times(a0, w)  this vector must be zero
// it involves a0*s2f with coefficient (al-2*bt)/(2*al), hence we can express a0*s2f

Mult[3][8]=-2*al*Times(a0, w)[1]/(al-2*bt);
Mult[8][3]=Mult[3][8];

//
// Express s1*s1
//

// a0*(u1*u1+u1*v1)=al*u1*v1, where the right side has -s1*s1/al

vector s1s1=-al*(Times(a0,uu+uv)-al*uv);
Mult[6][6]=s1s1;

//
// Express a3 and am3
//

// s1*s1 contains am2 times bt*(al-bt)^2*(al-4*bt)/(4*(al-2*bt))
//
// so fold(s1*s1)-s1*s1=0 and it contains a3 times the same

vector A3=-4*(al-2*bt)*(fold(s1s1-bt*((al-bt)^2)*
     (al-4*bt)*am2/(4*(al-2*bt)))-s1s1)/
     (bt*((al-bt)^2)*(al-4*bt));
     
// Update function f

proc f (vector v)
{
poly v1=v[1];
poly v2=v[2];
poly v3=v[3];
poly v4=v[4];
poly v5=v[5];
poly v6=v[6];
poly v7=v[7];
poly v8=v[8];
poly ffv1=ff(v1);
poly ffv2=ff(v2); 
poly ffv3=ff(v3);
poly ffv4= ff(v4); 
poly ffv5=ff(v5); 
poly ffv6=ff(v6); 
poly ffv7=ff(v7); 
poly ffv8=ff(v8);
       vector s=ffv1*A3+ffv5*a[2]+ffv4*a[3]+ffv3*a[4]+ffv2*a[5]+ffv6*a[6]+ffv8*a[7]+ffv7*a[8];
        return(s);
          } 
     
// Express am3 and a4

vector Am3=tau0(A3);
vector A4=f(Am3);

// Define tau1

proc tau1(vector v)
{
vector s=v[1]*A4+v[2]*A3+v[3]*a2+v[4]*a1+v[5]*a0+v[6]*s1+v[7]*s2+v[8]*s2f;
 return(s); 
}

// Add products with s1

Mult[1][6]=(al-bt)*s1+(lm*(1-al)+bt*(al-bt-1))*a[1]+(1/2)*(al-bt)*bt*(Am3+a[2]);
Mult[6][1]=Mult[1][6];
Mult[5][6]=(al-bt)*s1+(lm*(1-al)+bt*(al-bt-1))*a[5]+(1/2)*(al-bt)*bt*(a[4]+A3);
Mult[6][5]=Mult[5][6];

//
// Obtaining relations on al, bt, lm, lmf for given lm2 and lm2f
//
// Express S3_0, S3_1, S3_2

vector S3_0=Times(a0,A3)-bt*(a0+A3);
vector S3_1=f(S3_0);
vector S3_2=tau1(S3_0);

// D=<tau0,f> should induce D_6 on {S3_0,S3_1,S3_2}
// hence the following must be relations

vector diff0=S3_2-tau0(S3_1);
vector diff1=f(diff0);
vector diff2=tau1(diff0);

vector doublediff0=tau0(diff0)-diff0;;
vector doublediff1=tau0(diff1)-diff1;; // seems to be equal to -doublediff0
vector doublediff2=tau0(diff2)-diff2;;

// here are some polynomial relations

poly poly1=lambda(diff0); // poly 1 in the paper
poly poly2=lambda(diff2); // poly 2 in the paper 

// function lambdb
proc lambdb(vector v)
{
poly l=lambda(f(v));
 return(ff(l)); 
}

poly  poly3=lambdb(diff0);


// complete the multiplication table

Mult[4][7]=f(Mult[3][8]);;
Mult[7][4]=Mult[7][4];;

Mult[2][7]=tau0(Mult[4][7]);;
Mult[7][2]=Mult[2][7];;

Mult[5][8]=f(Mult[2][7]);;
Mult[8][5]=Mult[5][8];;

Mult[1][8]=tau0(Mult[5][8]);;
Mult[8][1]=Mult[1][8];;

Mult[4][8]=f(Mult[3][7]);;
Mult[8][4]=Mult[4][8];;

Mult[2][8]=tau0(Mult[4][8]);;
Mult[8][2]=Mult[2][8];;

Mult[5][7]=tau1(Mult[3][7]);;
Mult[7][5]=Mult[5][7];;

Mult[1][7]=tau0(Mult[5][7]);;
Mult[7][1]=Mult[1][7];;

Mult[4][7]=tau0(Mult[2][7]);;
Mult[7][4]=Mult[4][7];;

Mult[1][4]=f(Times(a0, A3));;
Mult[4][1]=Mult[1][4];;

Mult[2][5]=tau0(Mult[1][4]);;
Mult[5][2]=Mult[2][5];

Mult[1][5]=f(tau0(f(Times(a0, A4))));;
Mult[5][1]=Mult[1][5];;

vector u2=-s2+(lm2-bt-al*lm2)*a0+((al-bt)/2)*(a2+am2);;  
vector v2=s2+(bt-lm2)*a0+bt*(a2+am2)/2;;  

vector u1u2=Times(u1, u2)[1]; // contains [6][7] with coefficient 1/al
vector v1u2=Times(v1, u2)[1]; // contains [6][7] with coefficient -1/al

// we obtain the products s1*s2,  s1*s2f, and s2*s2 with the method described in Proposition 5.10
vector p12=u1u2+v1u2;;
Mult[6][7]=al*Times(v1, u2)[1]-Times(a0, p12);;
Mult[7][6]=Mult[6][7];; 
Mult[6][8]=f(Mult[6][7]);;
Mult[8][6]=Mult[6][8];; 

vector u2u2=Times(u2, u2)[1];; // contains [7][7] with coefficient 1
vector v2u2=Times(v2, u2)[1];; // contains [7][7] with coefficient -1
vector p22=u2u2+v2u2;;
Mult[7][7]=Times(v2, u2)[1]-Times(a0, p22)/al;;
Mult[8][8]=f(Mult[7][7]);;

// finally we compute s2*s2f. A3*A3-A3 must be the zero vector and it contains s2*s2f

Mult[7][8]=(A3-Times(A3,A3)[1])/(2*Times(A3,A3)[2][2]);;
Mult[8][7]=Mult[7][8];;

//////// one more polynomial

poly poly4=lambda(Times(A4,A4)-A4);
poly poly5=ff(poly4);

// polynomisl q1 and q2
map val=F, lm, lm, lm2, lm2;
poly q1=val(poly1);
poly q2=val(poly4);

poly resq=resultant(q1,q2, lm2);
 factorize(resq);
[1]:
   _[1]=-9331200/2401
   _[2]=64*lm-1
   _[3]=lm-1
   _[4]=lm
   _[5]=256*lm-13
   _[6]=256*lm-5
   _[7]=32*lm-1
   _[8]=128*lm-3
   _[9]=8*lm-1
[2]:
   1,2,1,1,1,1,1,1,1
   
// we check that the common solutions of polynomials p1,p3, p4,p5, with lm2, lm2f in the following set L are the 9 solutions listed.

list L= 1, 0, 1/8, 1/32, 1/64, 13/256, 3/128, 5/256;

// 

for (int i = 1; i <= 8; i=i+1)
       { 
        for (int j = 1; j<= 8; j=j+1)
        { 
            poly p5=lm2-L[i];
            poly p6=lm2f-L[j];
            ideal I=poly1, poly3, poly4, poly5, p5,p6;
            ideal sI=std(I);
            int h=vdim(sI);
            list l=L[i], L[j], h;
            if (h<>0)
            {
           solve(sI);
            print(l);
            }
      }
 }


 


