/* Like-for-like raw-C baseline for adtbuild: build a real singly-linked list of
 * N nodes (one malloc/node, the same allocation the Kappa cons spine must do),
 * then fold it. This is the HONEST comparison — the Kappa version also has to
 * allocate one cons cell per element; the gap to measure is the EXTRA closure/
 * env allocation Kappa adds (gap P0-A), not the list cells themselves.
 * (Uses malloc, never freed — a short-lived process, like the bench.) */
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
struct node { int64_t v; struct node *next; };
int main(int argc, char **argv) {
  int64_t n = argc > 1 ? (int64_t)atoll(argv[1]) : 2000000;
  struct node *head = 0;
  for (int64_t i = 1; i <= n; i++) {
    struct node *c = (struct node *)malloc(sizeof(struct node));
    c->v = i; c->next = head; head = c;
  }
  volatile int64_t acc = 0;
  for (struct node *p = head; p; p = p->next) acc += p->v;
  printf("%lld\n", (long long)acc);
  return 0;
}
