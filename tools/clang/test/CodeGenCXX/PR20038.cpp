// RUN: %clang_cc1 -triple %itanium_abi_triple -g -mllvm -no-discriminators -emit-llvm  %s -o - | FileCheck %s

struct C {
  ~C();
};
extern bool b;
// CHECK: call {{.*}}, !dbg [[DTOR_CALL1_LOC:![0-9]*]]
// CHECK: call {{.*}}, !dbg [[DTOR_CALL2_LOC:![0-9]*]]
// CHECK: [[FUN1:.*]] = !MDSubprogram(name: "fun1",{{.*}} isDefinition: true
// CHECK: [[FUN2:.*]] = !MDSubprogram(name: "fun2",{{.*}} isDefinition: true
// CHECK: [[DTOR_CALL1_LOC]] = !MDLocation(line: [[@LINE+1]], scope: [[FUN1]])
void fun1() { b && (C(), 1); }
// CHECK: [[DTOR_CALL2_LOC]] = !MDLocation(line: [[@LINE+1]], scope: [[FUN2]])
bool fun2() { return (C(), b) && 0; }
