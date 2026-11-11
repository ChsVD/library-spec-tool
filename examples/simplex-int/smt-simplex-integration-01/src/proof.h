#ifndef PROOF_H
#define PROOF_H 1
#include<stdlib.h>

enum rule{
      TRANS = 1, REFL, CONG, ASSUM, RESOL
};

enum ConclType {
    UF_EQ = 1, SAT_CL
};
typedef enum rule rule;
typedef struct Proof_node Proof_node;
typedef struct proof_node proof_node;

typedef struct{
    int left1;
    int left2;
    int right;
}concl_equation;

typedef struct {
    int* clause;
    int num;
}concl_clause;

struct Proof_node{
    rule identifier;           //表示rule
    int args_num;
    Proof_node** args;
    concl_equation concl;
};

Proof_node* proof_initialize(rule id, int left1, int left2, int right);

// struct proof_node{
//     rule identifier;           //表示rule
//     int args_num;
//     Proof_node** args;
//     ConclType t;
//     union {
//         concl_equation* concl;
//         concl_clause* cl;
//     } p;
// };

// proof_node* proof_initialize(rule id, int num, ConclType ctype, void* concl);
#endif