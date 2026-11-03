/* Linux x86-64 native instruction oracle. No libc, KVM, or root required.
 * Uses the Linux x86-64 syscall/UAPI register layouts. The only traced process
 * is our own forked child. Code executes in ring 3, with CS selecting 32/64 bits.
 * Input: count:u64 followed by the existing 440-byte x86-64 vector records.
 * Output preserves raw Linux signal information, registers, CS and SIMD state;
 * it does not compute any instruction result or infer exception vectors.
 */
typedef unsigned long long u64;
typedef unsigned int u32;
typedef unsigned short u16;
typedef unsigned char u8;
void *memcpy(void *dst,const void *src,unsigned long n) {
 u8 *d=dst;const u8 *s=src;for(unsigned long i=0;i<n;i++)d[i]=s[i];return dst;
}
struct regs {
 u64 r15,r14,r13,r12,rbp,rbx,r11,r10,r9,r8,rax,rcx,rdx,rsi,rdi,orig_rax;
 u64 rip,cs,flags,rsp,ss,fs_base,gs_base,ds,es,fs,gs;
};
struct fpregs {
 u16 cwd,swd,ftw,fop;
 u64 rip,rdp;
 u32 mxcsr,mask,st[32],xmm[64],padding[24];
};
struct vector { u8 code[16]; u64 r[16],flags; u32 seed,mode; u64 pte[2],xmm[32]; u32 mxcsr,pad; };
_Static_assert(sizeof(struct regs)==216,"Linux register layout");
_Static_assert(sizeof(struct fpregs)==512,"Linux FXSAVE layout");
_Static_assert(sizeof(struct vector)==440,"vector layout");
static long child;
static long call(long n,long a,long b,long c,long d,long e,long f) {
 register long r10 __asm__("r10")=d, r8 __asm__("r8")=e, r9 __asm__("r9")=f;
 long result;
 __asm__ volatile("syscall":"=a"(result):"a"(n),"D"(a),"S"(b),"d"(c),"r"(r10),"r"(r8),"r"(r9):"rcx","r11","memory");
 return result;
}
static void write_all(int fd,const char *p,u64 n) {
 while(n) { long k=call(1,fd,(long)p,n,0,0,0); if(k==-4) continue; if(k<=0) call(60,1,0,0,0,0,0); p+=k;n-=k; }
}
static void text(int fd,const char *s) {u64 n=0;while(s[n])n++;write_all(fd,s,n);}
static void hex(int fd,u64 value) {
 char out[17];for(int i=0;i<16;i++)out[i]="0123456789abcdef"[(value>>(60-4*i))&15];out[16]=' ';
 write_all(fd,out,17);
}
static void finish(int status) {
 if(child>0) {call(62,child,9,0,0,0,0);call(61,child,0,0,0,0,0);}
 call(60,status,0,0,0,0,0); __builtin_unreachable();
}
static void fail(const char *operation,long result) {
 text(2,"ERROR: ");text(2,operation);text(2," (negative errno in hex: ");hex(2,(u64)result);text(2,")\n");finish(1);
}
static void read_all(void *p,u64 n) {
 u8 *b=p;while(n) {long k=call(0,0,(long)b,n,0,0,0);if(k==-4)continue;if(k<=0)fail("truncated input",k);b+=k;n-=k;}
}
static void trace(long request,void *data) {
 long r=call(101,request,child,0,(long)data,0,0);if(r<0)fail("ptrace request",r);
}
static int wait_stop(void) {
 int status;long r;
 do {r=call(61,child,(long)&status,0,0,0,0);}while(r==-4);
 if(r<0 || (status&255)!=127)fail("child did not stop",r<0?r:status);
 return (status>>8)&255;
}
static void set_regs(struct regs *r,const struct vector *v) {
 r->rax=v->r[0];r->rcx=v->r[1];r->rdx=v->r[2];r->rbx=v->r[3];r->rsp=v->r[4];r->rbp=v->r[5];r->rsi=v->r[6];r->rdi=v->r[7];
 r->r8=v->r[8];r->r9=v->r[9];r->r10=v->r[10];r->r11=v->r[11];r->r12=v->r[12];r->r13=v->r[13];r->r14=v->r[14];r->r15=v->r[15];
 r->orig_rax=(u64)-1;r->rip=0x20100;r->flags=(r->flags&~0xdd5ull)|(v->flags&0xdd5);
}
void start(u64 *stack) {
 if(stack[0]!=2) {text(2,"usage: oracle i386|x86_64 < native.bin\n");finish(2);}
 const char *arch=(const char *)stack[2];int compat=arch[0]=='i';
 u64 count;read_all(&count,8);if(!count || count>1000000)fail("invalid count",0);
 /* Shared physical page: parent writes while child is stopped; child maps RX. */
 long mapping=call(9,0x20000,4096,3,0x21,-1,0);
 if(mapping!=0x20000)fail("cannot map code at 0x20000",mapping);
 u8 *code=(u8 *)mapping;
 long parent=call(39,0,0,0,0,0,0);
 child=call(57,0,0,0,0,0,0);if(child<0)fail("fork",child);
 if(child==0) {
  long r=call(157,1,9,0,0,0,0);if(r<0)fail("PR_SET_PDEATHSIG",r);
  if(call(110,0,0,0,0,0,0)!=parent)finish(1);
  r=call(10,mapping,4096,5,0,0,0);if(r<0)fail("mprotect RX",r);
  r=call(101,0,0,0,0,0,0);if(r<0)fail("PTRACE_TRACEME (parent tracing must be permitted)",r);
  call(62,call(39,0,0,0,0,0,0),19,0,0,0,0);finish(1);
 }
 if(wait_stop()!=19)fail("initial SIGSTOP",0);
 trace(0x4200,(void *)0x100000); /* PTRACE_SETOPTIONS, EXITKILL */
 struct regs base;struct fpregs fpbase;
 trace(12,&base);trace(14,&fpbase);
 if(base.cs!=0x33 || base.ss!=0x2b)fail("unexpected Linux user selectors",base.cs);
 text(1,"BEGIN ");hex(1,count);text(1,"\n");
 for(u64 index=0;index<count;index++) {
  struct vector v;read_all(&v,sizeof(v));
  if(v.code[0]<1 || v.code[0]>15)fail("bad instruction length",v.code[0]);
  for(int i=0;i<4096;i++)code[i]=0xcc;
  for(int i=0;i<v.code[0];i++)code[256+i]=v.code[1+i];
  struct regs r=base;struct fpregs fp=fpbase;
  set_regs(&r,&v);
  if(compat) {r.cs=0x23;r.ds=r.es=r.ss=0x2b;r.fs=r.gs=0;}
  fp.mxcsr=v.mxcsr;
  for(int i=0;i<32;i++){fp.xmm[2*i]=(u32)v.xmm[i];fp.xmm[2*i+1]=(u32)(v.xmm[i]>>32);}
  trace(13,&r);trace(15,&fp); /* SETREGS / SETFPREGS */
  /* Verify the kernel accepted all tested inputs before executing anything. */
  struct regs before;struct fpregs fpbefore;trace(12,&before);trace(14,&fpbefore);
  if(before.cs!=r.cs || before.rip!=r.rip || (before.flags&0xdd5)!=(r.flags&0xdd5))fail("register setup not accepted",index);
  const u64 *got=(const u64 *)&before,*want=(const u64 *)&r;
  for(int i=0;i<16;i++)if(got[i]!=want[i])fail("GPR setup not accepted",index);
  if(before.rsp!=r.rsp || fpbefore.mxcsr!=fp.mxcsr)fail("RSP/MXCSR setup not accepted",index);
  for(int i=0;i<(compat?32:64);i++)if(fpbefore.xmm[i]!=fp.xmm[i])fail("XMM setup not accepted",index);
  trace(7,0);int sig=wait_stop(); /* CONT: preserve vector's TF; no injected single-step. */
  int info[32];trace(0x4202,info);trace(12,&r);trace(14,&fp);
  if(info[0]!=sig)fail("signal information disagrees",sig);
  hex(1,index);hex(1,sig);hex(1,(u32)info[2]);hex(1,r.rip);hex(1,r.cs);hex(1,r.flags);
  u64 gpr[16]={r.rax,r.rcx,r.rdx,r.rbx,r.rsp,r.rbp,r.rsi,r.rdi,r.r8,r.r9,r.r10,r.r11,r.r12,r.r13,r.r14,r.r15};
  for(int i=0;i<16;i++)hex(1,gpr[i]);
  for(int i=0;i<32;i++)hex(1,fp.xmm[2*i]|((u64)fp.xmm[2*i+1]<<32));
  hex(1,fp.mxcsr);text(1,"\n");
 }
 u8 extra;if(call(0,0,(long)&extra,1,0,0,0)!=0)fail("trailing input",0);
 text(1,"END\n");finish(0);
}
