#include <iostream>
#include <cmath>
#include <cassert>

void demo1(float val, int exponent)
{
    float result1 = pow(val, exponent);
    std::cout << "Result: " << result1 << std::endl;
    float result2 = 1.0;
    for (int i = 0; i < exponent; ++i)
    {
        result2 *= val;
    }
    std::cout << "Result using loop: " << result2 << std::endl;
    assert(result1 == result2); // Ensure both methods yield the same result
}

int main()
{
    float value = 2.0f;
    int exp = 3;
    demo1(value, exp);
    return 0;
}