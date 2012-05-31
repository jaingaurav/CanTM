CanTM
=====

git clone git@github.com:jaingaurav/CanTM.git

mkdir CanTM-build

cd CanTM-build

../CanTM/llvm/configure

make

export PATH=(PATH TO CanTM directory)/Release+Asserts/bin:$PATH

clang++ -S -emit-llvm ../CanTM/tests/test1.cpp

opt -load Release+Asserts/lib/LLVMCanTM.dylib -CanTM < test1.s > test1.bc

lli test1.bc

