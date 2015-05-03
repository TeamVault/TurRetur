#include "classes.h"
#include <iostream>

A::~A() { std::cout << "deleted A" << std::endl; }
void A::f() { std::cout << "A::f" << std::endl; }
//void A::g() { std::cout << "A::g" << std::endl; }
void A::h() { std::cout << "A::h" << std::endl; }

B::~B() { std::cout << "deleted B" << std::endl; }
void B::f() { std::cout << "B::f" << std::endl; }
void B::g() { std::cout << "B::g" << std::endl; }

C::~C() { std::cout << "deleted C" << std::endl; }
void C::f() { std::cout << "C::f" << std::endl; }
void C::h() { std::cout << "C::h" << std::endl; }

D::~D() { std::cout << "deleted D" << std::endl; }
void D::g() { std::cout << "D::g" << std::endl; }
void D::t() { std::cout << "D::t" << std::endl; }
void D::f() { std::cout << "D::f" << std::endl; }
void D::h() { std::cout << "D::h" << std::endl; }
