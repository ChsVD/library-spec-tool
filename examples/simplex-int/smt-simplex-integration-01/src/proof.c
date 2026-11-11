#include"proof.h"

Proof_node* proof_initialize(rule id, int left1, int left2, int right){
    Proof_node* p = (Proof_node*)malloc(sizeof(Proof_node));
    p->identifier = id;
    if(id == TRANS){
        p->args_num = 2;}
    else if(id == CONG){
        p->args_num = 4;}
    else {
        p->args_num = 0;}
    p->args = (Proof_node**)malloc((p->args_num)*sizeof(Proof_node*));
    p->concl.left1 = left1;
    p->concl.left2 = left2;
    p->concl.right = right;
    return p;
}