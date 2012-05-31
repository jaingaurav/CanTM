CanTM
=====

CanTM


mkdir CanTM-build
cd CanTM-build
../CanTM/llvm/configure
make
export PATH=/Volumes/Extras/Development/CanTM-build/Release+Asserts/bin:$PATH
clang++ -S -emit-llvm ../CanTM/tests/test1.cpp
opt -load Release+Asserts/lib/LLVMCanTM.dylib -CanTM < test1.s > /dev/null

