/* xlang/binarytrees reference — C (-O2). N = depth = 18 HARDCODED.
 *
 * Binary-trees (CLBG-style): allocate + traverse many binary trees up to a
 * given depth and print the check sums. This is the canonical allocation /
 * GC-pressure microbenchmark.
 *
 * METHODOLOGY: idiomatic-but-fair, NOT the hyper-tuned CLBG entry. Each tree
 * node is a heap allocation (malloc) with two child pointers; we deliberately
 * do NOT use a bump/arena allocator, object pool, or parallelism, because the
 * point is to exercise the allocator the way an idiomatic functional program
 * would (one allocation per node, freed by walking the tree). This is the fair
 * cross-language counterpart to the Kappa/Go/Haskell ports, which each allocate
 * one heap node per tree node via their own runtime/GC.
 *
 * Output is a SINGLE line so the harness measures compute+alloc, not I/O:
 *   stretch <s> trees <t> longlived <l>
 * where
 *   s = itemCheck of the stretch tree (depth maxDepth+1)
 *   t = sum over depths d in {minDepth, minDepth+2, ..., maxDepth} of the total
 *       itemCheck across all 2^(maxDepth-d+minDepth) trees built at that depth
 *   l = itemCheck of the long-lived tree (depth maxDepth)
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

typedef struct Node {
    struct Node *left;
    struct Node *right;
} Node;

/* depth = 18 HARDCODED (N) */
#define MIN_DEPTH 4
#define MAX_DEPTH 18

static Node *bottom_up_tree(int depth) {
    Node *n = (Node *)malloc(sizeof(Node));
    if (depth > 0) {
        n->left = bottom_up_tree(depth - 1);
        n->right = bottom_up_tree(depth - 1);
    } else {
        n->left = NULL;
        n->right = NULL;
    }
    return n;
}

static int64_t item_check(const Node *n) {
    if (n->left == NULL) {
        return 1;
    }
    return 1 + item_check(n->left) + item_check(n->right);
}

static void free_tree(Node *n) {
    if (n->left != NULL) {
        free_tree(n->left);
        free_tree(n->right);
    }
    free(n);
}

int main(void) {
    int min_depth = MIN_DEPTH;
    int max_depth = MAX_DEPTH;
    int stretch_depth = max_depth + 1;

    /* stretch tree */
    Node *stretch = bottom_up_tree(stretch_depth);
    int64_t stretch_check = item_check(stretch);
    free_tree(stretch);

    /* long-lived tree built first, checked last */
    Node *long_lived = bottom_up_tree(max_depth);

    int64_t trees_total = 0;
    for (int depth = min_depth; depth <= max_depth; depth += 2) {
        int64_t iterations = (int64_t)1 << (max_depth - depth + min_depth);
        int64_t check = 0;
        for (int64_t i = 0; i < iterations; i++) {
            Node *t = bottom_up_tree(depth);
            check += item_check(t);
            free_tree(t);
        }
        trees_total += check;
    }

    int64_t long_lived_check = item_check(long_lived);
    free_tree(long_lived);

    printf("stretch %lld trees %lld longlived %lld\n",
           (long long)stretch_check,
           (long long)trees_total,
           (long long)long_lived_check);
    return 0;
}
