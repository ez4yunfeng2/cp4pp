#include <iostream>
extern "C"{
    int entry(int);
}
int main(int argc,char** argv){
    int a = entry(101);
    std::cout<<"\nReturn: "<<a;
}