#include <iostream>
#include <string>

extern std::string foo();

int main(void) { std::cout << foo() << std::endl; }
