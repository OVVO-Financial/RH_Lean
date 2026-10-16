// Exact C++/unsigned-128 fixed-point Nyman–Beurling finite witness.
// Build from repository root:
// c++ -std=c++17 -O3 experiments/nyman_beurling/certify_N96.cpp -o /tmp/certify_N96
// /tmp/certify_N96
// This certifies a single finite rational upper bound, NOT RH or d_N -> 0.
#include <array>
#include <cstdint>
#include <iostream>
#include <stdexcept>
using u128=unsigned __int128;
constexpr uint64_t P=(1u<<20), T=3000000, SCALE=(1ull<<48);
constexpr int N=96;
constexpr std::array<int64_t,N-1> q={
#include "n96_coeffs.inc"
};
static void print_u128(u128 x){
 if(!x){std::cout<<'0';return;}
 char s[128];int n=0;
 while(x){s[n++]=(char)('0'+x%10);x/=10;}
 while(n--)std::cout<<s[n];
}
int main(){
 u128 partial=0;
 uint64_t l1_numer=0;
 for(int k=2;k<=N;k++){
   int64_t v=q[k-2];l1_numer+=(uint64_t)k*(v<0?-v:v);
 }
 uint64_t maximal_num=P+l1_numer;
 // Since |P-sum q_k*(m mod k)|<=maximal_num, all products below
 // are <(2^48)*(maximal_num^2)+P^2*T*(T+1)<2^128.
 for(uint64_t m=1;m<=T;m++){
   int64_t num=(int64_t)P;
   for(int k=2;k<=N;k++)num-=q[k-2]*(int64_t)(m%k);
   if((u128)(num<0?-num:num)>maximal_num)
     throw std::runtime_error("residual numerator bound failed");
   u128 a=(u128)(num<0?-num:num);
   u128 numer=(u128)SCALE*a*a;
   u128 den=(u128)P*P*m*(m+1);
   partial+=(numer+den-1)/den;
 }
 u128 tail_n=(u128)SCALE*maximal_num*maximal_num;
 u128 tail_d=(u128)P*P*(T+1);
 u128 tail=(tail_n+tail_d-1)/tail_d;
 u128 total=partial+tail;
 std::cout<<"N="<<N<<" P="<<P<<" T="<<T<<" SCALE="<<SCALE<<"\n";
 std::cout<<"partial_ceiled=";print_u128(partial);std::cout<<"\n";
 std::cout<<"tail_ceiled=";print_u128(tail);std::cout<<"\n";
 std::cout<<"total_ceiled=";print_u128(total);std::cout<<"\n";
 std::cout<<"l1_numerator="<<l1_numer<<"\n";
 std::cout<<"less_than_1_over_92="<<(92*total<SCALE?"PASS":"FAIL")<<"\n";
 return 92*total<SCALE ? 0:1;
}
