// CN test: Struct field write with frame reasoning
// From cn-tutorial: struct_1.c
// Tests: RW<struct s> resource, struct field access in spec (.x, .y),
//        frame property (unchanged field preserved)
// NEEDS: RW resource type, struct field access in spec postcondition

struct s
{
  int x;
  int y;
};

void set_y(struct s *p)
/*@ requires take StructPre = RW<struct s>(p);
    ensures
      take StructPost = RW<struct s>(p);
      StructPre.x == StructPost.x;
      StructPost.y == 0i32; @*/
{
  p->y = 0;
}

int main(void)
{
  struct s val;
  val.x = 1;
  val.y = 2;
  set_y(&val);
  return val.x;
}
