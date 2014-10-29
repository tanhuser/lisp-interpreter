#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
#include <string.h>
#include <math.h> 
#include <stdarg.h>
#include <setjmp.h>
#define MAX_NAME 256
#define INITIAL_HEAP_SIZE 64000
#define STACK_SIZE (160 * 1024)
#define ENV_SIZE (160 * 1024)

typedef uint8_t uint8;
typedef uint64_t value_t;
typedef int number_t;
typedef uint8_t hash_t;
typedef uint64_t type_t;

const int MAX_HASH = 255;
hash_t string_hash (const char *str)
{
  hash_t hash = 7;
  for (int i = 0; str[i] != '\0'; i++)
    hash += (unsigned char)str[i];
  return (hash_t)(hash % MAX_HASH);	
}

#define TAG_NUM 0x0
#define TAG_LIST 0x1
#define TAG_SYM 0x2
#define TAG_OTHER 0x3

#define TYPE_NUM 0x0
#define TYPE_LIST 0x1
#define TYPE_SYM 0x2
#define TYPE_BUILTIN 0x3

#define UNBOUND ((value_t) TAG_SYM)
#define EMPTY_LIST ((value_t) TAG_LIST)
#define RELOCATED_MARK ((value_t)0x000101) 
#define END RELOCATED_MARK
#define tag(x) ((x)&0x3)
#define ptr(x) ((void*)((x) & ~(value_t)0x3))
#define tagptr(x, t) (((value_t)(x)) | (t))
#define number(x) (((value_t)(x)) << 2)
#define sym_val(x) ((Symbol*)(ptr(x)))
#define list_val(x) ((List *)ptr(x))
#define builtin_val(x) ((Builtin *)ptr(x))
#define is_num(x) (tag(x) == TAG_NUM)
#define is_list(x) (tag(x) == TAG_LIST)
#define is_spec(x) (tag(x) == TAG_SPEC)
#define is_sym(x) (tag(x) == TAG_SYM)
#define list(x) (tagptr((x), TAG_LIST))
#define type(x) *((type_t*)x)
#define error(...) do { printf(__VA_ARGS__); fprintf(stderr,"\n"); fail();} while(0);
#define head(l) (safe_listval(l)->head)
#define tail(l) (safe_listval(l)->tail)
#define head_(l) (list_val(l)->head)
#define tail_(l) (list_val(l)->tail)
#define assert(cond, ...) do {if (!(cond)) error(__VA_ARGS__);} while(0);
#define str(x) _str(x)
#define _str(x) #x
#define assert_type(val, type) assert(type_of(val) == TYPE_##type, "Error: expected " str(type))
#define NL do {printf("\n");} while(0);

  typedef struct {
    type_t type;
  } Type;

typedef struct {
  value_t head;
  value_t tail;
} List;

typedef struct Symbol {
  value_t binding;
  hash_t hash;
  struct Symbol *left;
  struct Symbol *right;
  char name[1];
} Symbol;


typedef enum {
  B_FN = 0, B_MACRO, B_QUOTE, B_COND, B_DO, B_DEF, B_AND, B_OR, 
  F_ADD, F_SUB, F_DIV, F_MUL, F_LT, F_GT, F_EQ, F_NOT, F_CONS, F_HEAD, F_TAIL, 
  F_EVAL, F_APPLY,
  F_LISTP, F_SYMBOLP, F_NUMBERP, F_BUILTINP, F_PRINT, N_BUILTINS
} BuiltinCode;

const char builtin_names[][10] = {
  "fn", "macro", "quote", "cond", "do", "def", "and", "or", 
  "+", "-", "/", "*", "<", ">", "=", "not", "cons", "head", "tail",
  "eval", "apply",
  "list?", "symbol?", "number?", "builtin?", "print"
};	

value_t FN, MACRO, NIL, T, QUOTE, REST, UNQUOTE, QUASIQUOTE, UNQUOTE_SPLICING;


char *heap, *newheap, *curheap, *lim, *gc_tresh;
float heap_resize_ratio = 2;
int heap_size;

value_t *stack;
int curstack = 0, stack_size = STACK_SIZE;

value_t *env;
int curenv = 0, env_size = ENV_SIZE;

typedef struct {
  type_t type;
  BuiltinCode code;
} Builtin;

Builtin builtins[N_BUILTINS];

Symbol *symtab = NULL;
// for error handling in REPL
jmp_buf jmp_mark;
bool in_repl = false;
void fail()
{
  if (in_repl)
    longjmp(jmp_mark, -1);
  else
    exit(1);
}
type_t type_of(value_t v)
{
  type_t t = tag(v);
  if (t < TAG_OTHER) return t;
  void *p = ptr(v); // TODO rise error on null
  return ((Type*)p)->type;
}

List *safe_listval(value_t v)
{
  if (v == EMPTY_LIST)
    error("Trying to take head/tail of empty list");
  return list_val(v);
}

number_t num_val(value_t x)
{
  assert_type(x, NUM);
  return (number_t)(x >> 2);  
}
/*
 *======================== GARBAGE COLLECTION ========================
 */

void print(value_t);
void *halloc(size_t);

value_t peek() { return stack[curstack - 1]; }

void push(value_t v)
{
  if (curstack >= stack_size)
    error("Stack overflow");
  stack[curstack] = v;
  curstack++;
}

value_t pop() { return stack[--curstack]; }

void env_push(value_t v)
{
  if (curenv >= env_size - 1) 
    error("Env overflow");
  env[curenv] = v;
  curenv++;
}

void restore_env(int ee) { curenv = ee; }

value_t env_pop() {	return env[--curenv]; }

value_t popn(int n)
{
  curstack -=n;
  return stack[curstack];
}

void restore_stack(int n) {	curstack = n; }

void push_reverse_list(value_t l)
{
  if (l == EMPTY_LIST)
    return;
  push_reverse_list(tail(l));
  push(head(l));
}

bool is_gc = 0;

void dump_symtab(Symbol *s)
{
  printf("%s :", s->name);
  print(s->binding);
  NL;
  if(s->left) {
    printf (" ");
    dump_symtab(s->left);
  }
  if(s->right) {
    printf(" ");
    dump_symtab(s->right);	
  }
}

void dump_heap()
{
  char *tmp = heap;
  while(tmp < curheap - sizeof(List)) {
    value_t val = ((List*)tmp)->head;
    print(val); 
    printf(" -|- ");
    tmp += sizeof(List);
  }
}

void dump_stack()
{
  int cur = 0;
  while (cur < curstack) {
    print(stack[cur]);
    cur++;
    printf("\t");
  }
  printf ("\n");
}

void dump_env()
{
  int cur = 0;
  while (cur < curenv) {
    print(env[cur]);
    cur++;
    printf("\t");
  }
  printf ("\n");
}

value_t make_cell(value_t v)
{

  push(v);
  List *cell = halloc(sizeof(List));
  cell->head = pop();
  cell->tail = EMPTY_LIST;
  return tagptr(cell, TAG_LIST);
}

void relocate_symtab(Symbol*);

value_t relocate(value_t);

void gc()
{
	
  if (is_gc)
    error("Gc in gc!!!!");
  is_gc = true;

  int oh = heap_size;
  heap_size = (int)(heap_size * heap_resize_ratio);
  if (newheap == NULL)
    newheap = malloc(heap_size);
  else
    newheap = realloc(newheap, heap_size);
  
  char *t = heap;
  heap = newheap;
  newheap = t;

  curheap = heap;
  lim = heap + heap_size;
  int ss = 0;
	

  //printf("before:"); dump_stack();
  while (ss < curstack) {
    stack[ss] = relocate(stack[ss]);
    ss++;
  }
  int ee = curenv - 2;

  while (ee >= 0) {
    if (type_of(env[ee] != TYPE_SYM))
      env[ee] = relocate(env[ee]);
    ee -= 2;
  }

  relocate_symtab(symtab);
	
  is_gc = false;
  // heap poisoning for trapping bugs
  memset(newheap, 0x0A, oh);

}

void relocate_symtab(Symbol *sym)
{
  sym->binding = relocate(sym->binding);
  if (sym->left)
    relocate_symtab(sym->left);
  if(sym->right)
    relocate_symtab(sym->right);
}


value_t relocate_list(value_t);
value_t _relocate_list(value_t l)
{
	
  value_t v = head(l);
  value_t t = tail(l);
  value_t cell = make_cell(relocate(v));
  if (t != EMPTY_LIST)
    tail(cell) = relocate_list(t);
  return cell;
}

value_t relocate_list(value_t l)
{
  if (l == EMPTY_LIST)
    return l;
  if (head(l) != RELOCATED_MARK) {
    tail(l) = _relocate_list(l);
    head(l) = RELOCATED_MARK;
  } 
  return tail(l);
}

value_t relocate(value_t v)
{
 switch(type_of(v)) {
  case TYPE_LIST:
    return relocate_list(v);
  default:
    return v;
  }
}

void *halloc(size_t s)
{
  if (curheap + s >= lim)
    gc();
  char *h = curheap; 
  curheap += s;
  return (void*)h;
}
/*
 * ========= SYMBOL AND CONS ==========================================
 */

value_t cons_(value_t h, value_t t)
{
  push(h);
  push(t);
  value_t cell = make_cell(UNBOUND);
  tail_(cell) = pop();
  head_(cell) = pop();
  return cell;
}

value_t cons(value_t h, value_t t)
{
  assert_type(t, LIST);
  return cons_(h,t);
}


Symbol *make_symbol(const char *name)
{
  Symbol *sym = malloc(sizeof(Symbol) + strlen(name));
  sym->binding = UNBOUND;
  sym->right = sym->left = NULL;
  sym->hash = string_hash(name);
  strcpy(sym->name, name);
  return sym;
}

// find symbol in an environment
Symbol *_find_symbol(const char *name, hash_t hash, Symbol *root)
{
  if (root == NULL)
    return NULL;
  if (hash == root->hash) {
    if (!strcmp(name, root->name))
      return root;
  }

  if (hash > root->hash)
    return _find_symbol(name, hash, root->right);
  return _find_symbol(name, hash, root->left);
}

Symbol *find_symbol(const char *name, Symbol **env)
{
  if (*env == NULL)
    return NULL;
  hash_t hash = string_hash(name);
  return _find_symbol(name, hash, *env);
}	

void _add_symbol(Symbol *sym, Symbol *root)
{
  if (sym->hash > root->hash) {
    if (root->right == NULL)
      root->right = sym;
    else
      _add_symbol(sym, root->right);
  } else {
    if (root->left == NULL)
      root->left = sym;
    else
      _add_symbol(sym, root->left);
  }
  return;
}

Symbol *add_symbol(const char *name, Symbol **env)
{
  Symbol *s = make_symbol(name);
  if (*env == NULL)
    *env = s;
  else
    _add_symbol(s, *env);
  return s;
}

Symbol *_symbol(const char *name, Symbol **env)
{
  Symbol *t = find_symbol(name, env);
  return t != NULL ? t : add_symbol(name, env);
}

value_t symbol(const char *name, Symbol **env)
{
  return tagptr(_symbol(name, env), TAG_SYM);
}

/*
 *================LIST FUNCTIONS ===================================
 */

static void push_list(value_t l)
{
  for (value_t v = l; v != EMPTY_LIST; v = tail_(v))
    push(head_(v));
}

static value_t pop_list(int ss)
{
  push(EMPTY_LIST);
  while (curstack > ss + 1) {
    value_t t = pop();
    value_t h = pop();
    push(cons_(h, t));
  }
  return pop();
}

static value_t make_list(value_t h, ...)
{
  va_list args;
  int ss = curstack;
  va_start(args, h);

  for (value_t v = h; v != END; v = va_arg(args, value_t)) {
    push(v);
  }
	
  va_end(args);
  return pop_list(ss);
}
/*
 * ========= READ FUNCTIONS ======================================
 */

static inline bool is_space(char c)
{
  return c == ' ' || c == '\t' || c == '\n';
}

static inline char fpeekc (FILE *f)
{
  char c = getc(f);
  /* printf("%c\n", c); */
  ungetc(c, f);
  return c;
}

void skip_spaces(FILE *f)
{
  char c = fgetc(f);
  while (is_space(c))
    c = getc(f);
  ungetc(c,f);
}

void read(FILE*, Symbol **env);

void read_sym(FILE *f, Symbol **env)
{
  char c;
  char buf[MAX_NAME];
  int i = 0;	
  do {
    c = getc(f);
  buf[i] = c;
    c = fpeekc(f);
    i++;
    if (i > MAX_NAME)
      error("name too long");
  } while(!is_space(c) && c != ')' && c != '(' && !feof(f));
  buf[i] = '\0';
  push(symbol(buf, env));
}

void read_int(FILE* f, Symbol **env)
{
  int n = 0;
  char c = fgetc(f);
  while (!is_space(c) && c!= ')' && c!='(') {
    n = 10 * n + c - 0x30;
    c = fgetc(f);
  }
  ungetc(c, f);
  push(number(n));
}

void read_list(FILE *f, Symbol **env)
{
  getc(f);
  char c = fpeekc(f);
  if (c == ')') {
    getc(f);
    push(EMPTY_LIST);
    return;
  }

  int ss = curstack;
  while (!feof(f)) {
    char c = fpeekc(f);
    if (c == ')') {
      getc(f);
      break;
    }
    if (is_space(c)) {
      skip_spaces(f);
      continue;
    }

    read(f, env);
    
  }
 push(pop_list(ss));
 /* skip_spaces(f); */
 /* printf("%c\n", fpeekc(f)); */

}

void read(FILE *f, Symbol **env)
{
  char c;
 start:
  c = fpeekc(f);
  switch(c) {
  case '(':
    read_list(f, env);
    break;
  case ' ': case '\n': case '\t':
    skip_spaces(f);
    goto start;
    return;
    break;
  case '\'':
    getc(f);
    read(f, env);
    push(make_list(QUOTE, pop(), END));
    break;
  case ',': {
    getc(f);
    char cc = fpeekc(f);
    value_t ut = UNQUOTE;
    if (cc == '@') {
      fgetc(f);
      ut = UNQUOTE_SPLICING;
    }
    read(f, env);
    push(make_list(ut, pop(), END));
  }
    break;
  case '`':
    getc(f);
    read(f, env);
    push(make_list(QUASIQUOTE, pop(), END));
    break;
  case '0': case '1': case '2': case '3': case '4':
  case '5': case '6': case '7': case '8': case '9':
    read_int(f, env);
    break;
  case ';':
    while (c != '\n')
      c = getc(f);
    //goto start;
    break;
  case ')':
    getc(f);
    error("Unmatched closing parentesis");
    break;
  default:
    read_sym(f, env);
    break;
  }
}


value_t read_file(const char *name)
{
  FILE *f = fopen(name, "rt");
  if (f == NULL) return UNBOUND;
  int ss = curstack;
  while (!feof(f)) {
    int ss = curstack;
    read(f, &symtab);
    if (ss != curstack) {
    value_t tmp = make_cell(UNBOUND);
    
    head(tmp) = pop();
    push(tmp);
    }
  }
  fclose(f);

  int ss1 = ss + 1;
  value_t cur = stack[ss];
  while (ss1 < curstack) {
    tail(cur) = stack[ss1];
    cur = stack[ss1];
    ss1++;
  }
  restore_stack(ss + 1);
  return pop();
}

/*
 * ========= PRINT FUNCTIONS ======================================
 */

void print(value_t v);

void print_list(value_t v)
{
  if (v == EMPTY_LIST) {
    printf("()");
    return;
  }
	
  if (head(v) == QUOTE) {
    printf("'"); 
    if (tail(v) != EMPTY_LIST)
    print(head(tail(v)));
    return;
  }
	  
  if (head(v) == QUASIQUOTE) {
    printf("`"); 
    if (tail(v) != EMPTY_LIST)
print(head(tail(v)));
    return;
  }


  if (head(v) == UNQUOTE) {
    printf(","); 
    if (tail(v) != EMPTY_LIST)
    print(head(tail(v)));
    return;
  }
  
  if (head(v) == UNQUOTE_SPLICING) {
    printf(",@"); 
    if (tail(v) != EMPTY_LIST)
print(head(tail(v)));
    return;
  }


  printf("(");
	
  if (head(v) == RELOCATED_MARK) {
    printf("Relocated"); print(tail(v));
    return;
  }

  while (1) {
    print(head(v));
    v = tail(v);
    if(v == EMPTY_LIST)
      break;
    printf(" ");
  }
  printf(")");
}


void print(value_t v)
{
  switch(type_of(v)) {
  case TYPE_LIST:
    print_list(v); break;
  case TYPE_NUM:
    printf("%d", num_val(v)); break;
  case TYPE_SYM:
    if (v == UNBOUND)
      printf("unbound");
    else
      printf("%s", sym_val(v)->name);
    break;
  case TYPE_BUILTIN:
    printf("#<builtin %s >",  builtin_names[builtin_val(v)->code]); break;
  default:
    printf("default"); break;
  }
}

/*
 * ========== EVAL FUNCTIONS ========================================
 */

value_t eqp(value_t v1, value_t v2)
{
  if (type_of(v1) != TYPE_LIST || type_of(v2) != TYPE_LIST)
    return v1 == v2 ? T : NIL;

  while (v1 != EMPTY_LIST && v2 != EMPTY_LIST) {
    if (head(v1) != head(v2))
      return NIL;
    v1 = tail(v1);
    v2 = tail(v2);
  }
  return v1 == v2 ? T : NIL;
}

static value_t eval(value_t);
static value_t expand(value_t);
static value_t eval_sexp(value_t, bool);
static value_t to_bool(value_t v)
{
  if (v == NIL || v == EMPTY_LIST)
    return NIL;
  return T;
}

void prepare_args(value_t args)
{
  int ss = curstack;
  push_list(args);

  for (int i = ss; i < curstack; i++)
    stack[i] = eval(stack[i]);
}

void prepare_env(value_t args, int ss)
{
  int sp = ss;
  if (is_list(args))
    for (value_t h = args; h != EMPTY_LIST; h = tail(h)) {

      if(head(h) != REST) {
	
      if (ss == curstack)
	error("Not enough args");
	env_push(stack[ss]);
	env_push(head(h));
	ss++;
      } else {
	args = head(tail(h));
	break;
      }
    }

  if (!is_list(args)){
    env_push(pop_list(ss));
    env_push(args);
  }
  restore_stack(sp);
}

static inline value_t eval_sym(value_t v)
{
  if (v == UNBOUND)
    error("Cannot eval unbound");
	
  for (int i = curenv - 1; i >= 0; i-=2) {
    if (env[i] == v) {
      //printf("Sym in env:"); print(v); print(env[i-1]); NL;
      return env[i-1];
    }
  }

  Symbol *sym = find_symbol(sym_val(v)->name, &symtab);
	
  return sym_val(v)->binding;
}

#define tail_eval(exp) do { sexp = (exp); restore_stack(ss); goto eval_top; } while(0);

void _assert_nargs(int _nargs, int n)
{
    assert(_nargs == n, "Error: too %s arguments", (_nargs > n ? "many" : "few"));
}

#define assert_nargs(n) _assert_nargs(nargs, (n))
value_t copy_body(value_t body)
{
  int ss = curstack;
  int sum, nargs;
  switch (type_of(body)) {
  case TYPE_LIST:
    if (body == EMPTY_LIST || head(body) == QUOTE) 
      return body;
    // check if it if a macro
    if(is_sym(head(body))) {
      push(body);
      value_t tmp = eval(head(body));
      
      body = pop();
      
      if (is_list(tmp) && head(tmp) == MACRO) {
	body = expand(body);
	return copy_body(body);
      }
    }
    // optimisation for not doing unnessessary copies
    if (curenv == 0)
      return body;

    push_list(body);
    for (int i = ss; i < curstack; i++) {
      stack[i] = copy_body(stack[i]);
    }
    return pop_list(ss);
  
  case TYPE_SYM:
    // replace symbol from its value from environment
    for (int i = curenv - 1; i > 0; i-=2)
      if (env[i] == body) {
	return env[i-1];
      }
    return body;
  
  default:
    return body;
  }
}

value_t eval (value_t v)
{
  return eval_sexp(v, false);
}

value_t expand(value_t v)
{
  return eval_sexp(v, true);
}

value_t eval_sexp(value_t sexp, bool noeval)
{
  value_t fun, funtype, args, body;
  BuiltinCode code;
  int nargs, sum;
  int ss = curstack, ee = curenv;

  int tail_macro = 1;
	
  value_t res = NIL;
  bool is_apply = false;
 eval_top:
  
  if (tail_macro > 0) tail_macro--;
  /* printf("Env:");  dump_env(); */
  /* print(sexp); NL; */
  switch (type_of(sexp)) {
  case TYPE_SYM:
    res = eval_sym(sexp);
    break;

  case TYPE_LIST:
    push(tail(sexp)); //args
    fun = eval(head(sexp));
  apply_top:    
    /* print(fun);  */
if (type_of(fun) == TYPE_BUILTIN)
      goto apply_builtin;

    if (type_of(fun) == TYPE_LIST) {
      args = (head(tail(fun))); //args
      body = tail(tail(fun)); //body
      goto apply;
    }
    print(fun);
    error("Applying not a function");
    break;
  default:
    res = sexp;
    break;
  }
  goto end;

 apply_builtin:
  code = builtin_val(fun)->code;
  args = pop();
  if(code >= F_ADD) {
    push_reverse_list(args);
    if(!is_apply)
for (int i = curstack - 1; i >= ss; i--)
      stack[i] = eval(stack[i]);
    is_apply=false;
  }
  nargs = curstack - ss;

  switch(code){
  case F_ADD:
    assert(nargs > 0, "Too few arguments");
    sum = num_val(pop());
    while (curstack > ss)
      sum += num_val(pop());
    res = number(sum);
    break;
  case F_SUB:
    assert(nargs > 0, "Too few arguments");
    sum = num_val(pop());
    if (nargs == 1) 
      sum = -sum;
    while (curstack > ss) {
      sum -= num_val(pop());
    }
    res = number(sum);
    break;
  case F_MUL:
    assert(nargs > 0, "Too few arguments");
    
    sum = num_val(pop());
    while (curstack > ss)
      sum *= num_val(pop());
    
    res = number(sum);
    break;

  case F_DIV:
    assert(nargs > 0, "Too few arguments");
    
    sum = num_val(pop());
    while (curstack > ss) {
      number_t num = num_val(pop());
      assert(num != 0, "Division by zero");
      sum /= num;
    }

    res = number(sum);
    break;
			
  case F_LT: {
    assert_nargs(2);
    number_t n1 = num_val(pop());
    number_t n2 = num_val(pop());
    if (n1 < n2)
      res = T;
    else
      res = NIL;
  }
    break;

  case F_GT: {
    assert_nargs(2);
    number_t n1 = num_val(pop());
    number_t n2 = num_val(pop());
    if (n1 > n2)
      res = T;
  }
    break;
 case F_EQ: {
    assert_nargs(2);
    value_t v1 = pop();
    value_t v2 = pop();
    res = eqp(v1, v2);
 }
    break;
  case F_NOT:
    assert_nargs(1);
if (pop() == NIL)
      res = T;
    else 
      res = NIL;
    break;
		
 case F_HEAD: {
    assert_nargs(1);
    value_t v = pop();
    assert_type(v, LIST);
    res = head(v);
 }
    break;

 case F_TAIL: {
    
    assert_nargs(1);
    
    assert_type(stack[ss], LIST);
    res = tail(stack[ss]);
 }
    break;
  case F_LISTP:
    assert_nargs(1);
    res = type_of(stack[ss]) == TYPE_LIST ? T : NIL;
    break;		

  case F_SYMBOLP:
    assert_nargs(1);
    res = type_of(stack[ss]) == TYPE_SYM ? T : NIL;
    break;	

  case F_NUMBERP:
    assert_nargs(1);
    res = type_of(stack[ss]) == TYPE_NUM ? T : NIL;
    break;		
		
  case F_BUILTINP:
    assert_nargs(1);
    res = type_of(stack[ss]) == TYPE_BUILTIN ? T : NIL;
    break;		
		
  case B_COND:
    push_list(args);
    for (int i = ss; i < curstack; ++i) {
      value_t pair = stack[i];
      value_t cond = head(pair);
      push(head(tail_(pair)));
      res = eval(cond);
      if (to_bool(res) != NIL) {
	if(tail_macro > 0) tail_macro++;
	tail_eval(pop());
	break;
      }
      pop();
    }
    break;
  case B_DEF: {
    const char *name = sym_val(head(args))->name;
    value_t sym = symbol(name, &symtab);
    res = eval(head(tail_(args)));
    sym_val(sym)->binding = res;
  }
    break;
  case B_OR: 
    push_reverse_list(args);
    while (curstack > ss) {
      res = eval(pop());
      if (res != NIL && res !=EMPTY_LIST)
	break;
    }
    break;
  case B_AND:
    push_reverse_list(args);
    while (curstack > ss) {
      res = eval(pop());
      if (res == NIL)
	break;
    }
    break;
  case F_PRINT:
    while (curstack > ss) {
  print(pop());
      NL;
    }
    break; 
  case F_EVAL:
    assert_nargs(1);
    res = eval(stack[ss]);
    break;
  case F_APPLY: {
    fun = pop();
    is_apply=true;
    goto apply_top;
  }
    break;
  
  case B_MACRO:
  case B_FN: {
    int ee1 = curenv;
    body = tail(args);
    args = head(args);
    push(args);
    // avoid unnessessary replacements while expanding macros    
    if (!(code == B_FN && noeval)) {
      if (is_list(args)) {
    // push arg symbols to env twice for shadowing
	for (value_t h = args; h != EMPTY_LIST; h = tail(h)) {
	  if(head(h) != REST) {
	    env_push(head(h));
	    env_push(head(h));
	  }
	}
      } else {
	env_push(args);
	env_push(args);
      }
    }
    body = copy_body(body);
    args = pop();
    res = cons_(code == B_FN ? FN : MACRO, cons_(args, body));
    restore_env(ee1);
  }
    break;
  case B_DO:
    push_reverse_list(args);
    while (curstack > ss) {
      res = eval(pop());
    }
    break;
  case F_CONS: {
    assert_nargs(2);
    value_t c1 = pop();
    value_t c2 = pop();
    res = cons(c1, c2);
    break;
  }
  case B_QUOTE:
    assert_nargs(0);
    res = head(args);
    break;
  default:
    error("Unknown builtin %d", code);
  }
  goto end;
 apply: {
    funtype = head(fun);
    assert(funtype == FN || funtype == MACRO, "Applying not a function!!!!!");
    value_t list = pop();
    push(body);
    push(args);
    int ss0 = curstack;
		
    push_list(list);

    for (int i = ss0; i < curstack; i++)
		
      if(funtype != MACRO && !is_apply)
	stack[i] = eval(stack[i]);
    is_apply = false;
    args = stack[ss0 - 1];
    restore_env(ee);

    prepare_env(args, ss0); // argnames
    args = pop();
    body = pop();

    push_reverse_list(body);

    while (curstack > ss) {

      if (curstack == ss + 1) {
	if (funtype == MACRO) {
	  tail_macro += 2;
	} else {
	  if (tail_macro) tail_macro++;
	}
	tail_eval(pop());
      } else {
	res = eval(pop());
      }
    }

  }
 end:
  if (tail_macro && !noeval) {
    tail_eval(res);
  }
  restore_stack(ss);
  restore_env(ee);
  return res;
}

value_t eval_toplevel(value_t l)
{
  value_t res = NIL;
  push_reverse_list(l);
  while (curstack != 0){
    value_t v = pop();
    res = eval(v);
  }
  return res;
}

void lisp_init()
{
  for (int i = 0; i < N_BUILTINS; ++i) {
    builtins[i].type = TYPE_BUILTIN;
    builtins[i].code = (BuiltinCode)i;
    Symbol *tmp = _symbol(builtin_names[i], &symtab);
    tmp->binding = tagptr(builtins + i, TAG_OTHER);
  }

  curheap = heap = malloc(INITIAL_HEAP_SIZE);
  lim = heap + INITIAL_HEAP_SIZE;
  heap_size = INITIAL_HEAP_SIZE;
  newheap = NULL;
	
  stack = malloc(stack_size * sizeof(value_t));
  env = malloc(env_size * sizeof(value_t));

  MACRO = symbol("macro", &symtab);
  FN = symbol("fn", &symtab);
  QUOTE = symbol("quote", &symtab);

  NIL = symbol("nil", &symtab);
  sym_val(NIL)->binding = NIL;

  T = symbol("#t", &symtab);
  sym_val(T)->binding = T;

  QUASIQUOTE = symbol("quasiquote", &symtab);
  UNQUOTE = symbol("unquote", &symtab);
  UNQUOTE_SPLICING = symbol("unquote-splicing", &symtab);
  REST = symbol("&", &symtab);
  sym_val(REST)->binding = REST;

}

int main()
{
  lisp_init();
  value_t sexp = read_file("system.lsp");
  eval_toplevel(sexp);
  in_repl = true;
  while (true) {
    NL;
    printf(">");
    int ss = curstack, ee = curenv;
    
    if (!setjmp(jmp_mark)) {
      read(stdin, &symtab);
      if (ss != curstack) {
      value_t res = eval(pop());
      print(res); 
      }
    } else {
      restore_stack(ss);
      restore_env(ee);
    } 
  }
  return 0;
}
