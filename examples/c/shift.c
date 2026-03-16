int main() {
    // char 类型的符号性（Signedness）在不同架构和操作系统下是不确定的。
    // kecc认为 char 是有符号的
    char a = 127;
    char b = a << 1;
    unsigned char c = (unsigned char)b >> 1;

    // 在 Docker arm架构的ubuntu中 char是unsigned char，所以b的值是254，c的值是0x7F
    // 因此会得到: clang (expected): 0, kecc: 1
    return b == -2 && c == 0x7F;
}
