/* Ring-3 instruction oracle. QEMU supplies instruction/exception semantics. */
typedef unsigned char u8;
typedef unsigned short u16;
typedef unsigned int u32;
typedef unsigned long long u64;
struct vec { u8 code[16]; u64 r[16], flags; u32 seed, mode; u64 pte[2], xmm[32]; u32 mxcsr, padding; };
_Static_assert(sizeof(struct vec)==440, "vector layout");
u64 ustate[17];
u64 xstate[32] __attribute__((aligned(16)));
u32 mxstate;
extern u64 gdt[];
extern void enter_user(void);
#define DECL(n) extern char isr##n[];
DECL(0) DECL(1) DECL(2) DECL(3) DECL(4) DECL(5) DECL(6) DECL(7) DECL(8) DECL(9)
DECL(10) DECL(11) DECL(12) DECL(13) DECL(14) DECL(15) DECL(16) DECL(17) DECL(18) DECL(19)
static char *isrs[] = {isr0,isr1,isr2,isr3,isr4,isr5,isr6,isr7,isr8,isr9,isr10,isr11,isr12,isr13,isr14,isr15,isr16,isr17,isr18,isr19};
static struct vec *vectors;
static u32 count, current;
static u64 idt[40];
static u8 tss[104];
static void out(u16 p,u8 v) { __asm__ volatile("outb %0,%1"::"a"(v),"Nd"(p)); }
static void put(char c) { out(0x3f8,c); }
static void str(const char *s) { while(*s) put(*s++); }
static void hex(u64 x) { for(int k=60;k>=0;k-=4) put("0123456789abcdef"[(x>>k)&15]); put(' '); }
static u32 random32(u32 *s) { u32 x=*s; x^=x<<13; x^=x>>17; x^=x<<5; return *s=x; }
static void next(void) {
 if(current==count) { str("END\n"); out(0xf4,0); for(;;) __asm__ volatile("hlt"); }
 struct vec *v=&vectors[current];
 u32 seed=v->seed;
 for(int k=0;k<8192;k+=4) *(u32 *)(0x8000ul+k)=random32(&seed);
 if(v->mode & 2) *(u64 *)0x8800=0x20180;
 for(int k=0;k<512;k++) *(u8 *)(0x20000ul+k)=0xcc;
 for(int k=0;k<15;k++) *(u8 *)(0x20100ul+k)=v->code[k+1];
 for(int k=0;k<16;k++) ustate[k]=v->r[k];
 ustate[16]=v->flags;
 for(int k=0;k<32;k++) xstate[k]=v->xmm[k];
 mxstate=v->mxcsr;
 *(volatile u64 *)0x6040=0x8000 | v->pte[0];
 *(volatile u64 *)0x6048=0x9000 | v->pte[1];
 __asm__ volatile("mov %0,%%cr3"::"r"(0x3000ul):"memory");
 __asm__ volatile("mov %0,%%cr0"::"r"(0x80000011ul | ((v->mode & 1)?0x10000:0)):"memory");
 enter_user();
}
struct frame {u64 r[16], vector, error, rip, cs, flags, rsp, ss;};
void record(struct frame *f) {
 u64 cr2; __asm__ volatile("mov %%cr2,%0":"=r"(cr2));
 u64 p0=*(volatile u64 *)0x6040, p1=*(volatile u64 *)0x6048;
 *(volatile u64 *)0x6040=0x8067; *(volatile u64 *)0x6048=0x9067;
 __asm__ volatile("mov %0,%%cr3"::"r"(0x3000ul):"memory");
 hex(current); hex(f->vector); hex(f->error); hex(f->rip-(f->vector==3));
 f->r[4]=f->rsp;
 for(int k=0;k<16;k++) hex(f->r[k]);
 hex(f->flags); hex(f->vector==14?cr2:0);
 u32 h=2166136261u; for(int k=0;k<8192;k++) {h^=*(u8 *)(0x8000ul+k);h*=16777619u;}
 hex(h); hex(p0); hex(p1);
 for(int k=0;k<32;k++) hex(xstate[k]);
 hex(mxstate); put('\n');
 current++; next();
}
void harness_main(u32 *mb) {
 u32 *mods=(u32 *)(u64)mb[6];
 vectors=(struct vec *)(u64)mods[0]; count=(mods[1]-mods[0])/sizeof(struct vec);
 out(0x21,0xff);out(0xa1,0xff);
 for(int k=0;k<20;k++) {
  u64 a=(u64)isrs[k];
  idt[2*k]=(a&0xffff) | (8ul<<16) | ((u64)(k==3?0xee:0x8e)<<40) | ((a&0xffff0000)<<32);
  idt[2*k+1]=a>>32;
 }
 *(u64 *)(tss+4)=0x78000;
 *(u16 *)(tss+102)=104;
 u64 a=(u64)tss;
 gdt[5]=103 | ((a&0xffffff)<<16) | (0x89ul<<40) | ((a&0xff000000)<<32);
 gdt[6]=a>>32;
 struct {u16 limit;u64 base;} __attribute__((packed)) id={sizeof(idt)-1,(u64)idt};
 __asm__ volatile("lidt %0; mov $0x28,%%ax; ltr %%ax"::"m"(id):"rax","memory");
 str("BEGIN ");hex(count);put('\n');
 next();
}
