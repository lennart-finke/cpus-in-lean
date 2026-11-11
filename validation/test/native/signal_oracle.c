/* Native Linux self-test using ordinary signal delivery. No process tracing.
 * ABI: Linux arch/x86/include/uapi/asm/sigcontext.h, asm-generic/ucontext.h.
 * A SIGUSR1 handler installs the instruction's input context. Its CPU exception
 * supplies the output context, then the handler restores the interrupted runner.
 * Both transitions use Linux's standard rt_sigreturn. No external process,
 * privileged device, tracing syscall, or expected model result is involved.
 */
typedef unsigned long long u64;
typedef unsigned int u32;
typedef unsigned short u16;
typedef unsigned char u8;
void *memcpy(void *dst,const void *src,unsigned long n) {
 u8 *d=dst;const u8 *s=src;for(unsigned long i=0;i<n;i++)d[i]=s[i];return dst;
}
struct fpregs {
 u16 cwd,swd,ftw,fop;u64 rip,rdp;u32 mxcsr,mask,st[32],xmm[64],reserved[24];
};
struct context {
 u64 r8,r9,r10,r11,r12,r13,r14,r15,rdi,rsi,rbp,rbx,rdx,rax,rcx,rsp,rip,flags;
 u16 cs,gs,fs,ss;
 u64 err,trapno,oldmask,cr2,fpstate,reserved[8];
};
struct stack {u64 pointer;u32 flags,padding;u64 size;};
struct ucontext {u64 flags,link;struct stack stack;struct context cpu;u64 sigmask;};
struct vector {u8 code[16];u64 r[16],flags;u32 seed,mode;u64 pte[2],xmm[32];u32 mxcsr,pad;};
#ifdef NATIVE_FP
/* FXSAVE order: logical ST(0)..ST(7), but FTW bits name physical registers. */
struct fp_input {u16 cw,sw,tw,pad;u64 reserved;u32 st[32];u8 memory[64];};
static struct fp_input fp_input;
_Static_assert(sizeof(struct fp_input)==208,"FP extension layout");
#endif
struct action {u64 handler,flags,restorer,mask;};
_Static_assert(sizeof(struct context)==256,"Linux sigcontext layout");
_Static_assert(__builtin_offsetof(struct ucontext,cpu)==40,"Linux ucontext layout");
_Static_assert(sizeof(struct fpregs)==512,"Linux FXSAVE layout");
_Static_assert(sizeof(struct vector)==440,"vector layout");
extern void signal_restorer(void);
static struct vector input;
static struct context recovery,observed;
static struct fpregs recovery_fp,observed_fp;
static volatile int phase;
static int observed_signal,observed_code,compat;
static long pid;
static u8 *code;
static long call(long n,long a,long b,long c,long d,long e,long f) {
 register long r10 __asm__("r10")=d,r8 __asm__("r8")=e,r9 __asm__("r9")=f;long result;
 __asm__ volatile("syscall":"=a"(result):"a"(n),"D"(a),"S"(b),"d"(c),"r"(r10),"r"(r8),"r"(r9):"rcx","r11","memory");
 return result;
}
static void finish(int status) {call(60,status,0,0,0,0,0);__builtin_unreachable();}
static void write_all(int fd,const char *p,u64 n) {
 while(n){long k=call(1,fd,(long)p,n,0,0,0);if(k==-4)continue;if(k<=0)finish(1);p+=k;n-=k;}
}
static void text(int fd,const char *s) {u64 n=0;while(s[n])n++;write_all(fd,s,n);}
static void hex(int fd,u64 v) {
 char b[17];for(int i=0;i<16;i++)b[i]="0123456789abcdef"[(v>>(60-4*i))&15];b[16]=' ';write_all(fd,b,17);
}
static void fail(const char *operation,long value) {
 text(2,"ERROR: ");text(2,operation);text(2," (value/negative errno: ");hex(2,(u64)value);text(2,")\n");finish(1);
}
static void read_all(void *p,u64 n) {
 u8 *b=p;while(n){long k=call(0,0,(long)b,n,0,0,0);if(k==-4)continue;if(k<=0)fail("truncated input",k);b+=k;n-=k;}
}
static void set_regs(struct context *c,const struct vector *v) {
 c->rax=v->r[0];c->rcx=v->r[1];c->rdx=v->r[2];c->rbx=v->r[3];c->rsp=v->r[4];c->rbp=v->r[5];c->rsi=v->r[6];c->rdi=v->r[7];
 c->r8=v->r[8];c->r9=v->r[9];c->r10=v->r[10];c->r11=v->r[11];c->r12=v->r[12];c->r13=v->r[13];c->r14=v->r[14];c->r15=v->r[15];
 c->rip=0x20100;c->cs=compat?0x23:0x33;c->ss=0x2b;c->flags=(c->flags&~0x50dd5ull)|(v->flags&0xdd5);
}
static void get_regs(const struct context *c,u64 *r) {
 r[0]=c->rax;r[1]=c->rcx;r[2]=c->rdx;r[3]=c->rbx;r[4]=c->rsp;r[5]=c->rbp;r[6]=c->rsi;r[7]=c->rdi;
 r[8]=c->r8;r[9]=c->r9;r[10]=c->r10;r[11]=c->r11;r[12]=c->r12;r[13]=c->r13;r[14]=c->r14;r[15]=c->r15;
}
static void mark_sse(struct fpregs *fp,u64 uc_flags) {
 /* The standard-layout XSAVE header follows the 512-byte FXSAVE region.
  * Set SSE present when editing its saved legacy fields. Preserve all other
  * feature bits, software metadata and extended state supplied by Linux. */
 if(!(uc_flags&1))return; /* UC_FP_XSTATE: plain FXSAVE has no XSAVE header. */
 if(fp->reserved[12]==0x46505853) {
  u32 extended=fp->reserved[13],size=fp->reserved[16];
  if(extended<580 || size<576 || extended>1024*1024)fail("invalid Linux xstate frame",extended);
  if(*(u32 *)((u8 *)fp+extended-4)!=0x46505845)fail("invalid xstate trailer",extended);
  *(u64 *)((u8 *)fp+512)|=
#ifdef NATIVE_FP
   3;
#else
   2;
#endif
 } else fail("missing xstate magic",fp->reserved[12]);
}
static void handler(int sig,int *info,struct ucontext *u) {
 struct context *c=&u->cpu;
 if(!c->fpstate)fail("missing signal FPU context",sig);
 struct fpregs *fp=(struct fpregs *)c->fpstate;
 if(phase==0 && sig==10) {
  if(c->cs!=0x33 || c->ss!=0x2b)fail("unexpected runner selectors",c->cs);
  recovery=*c;recovery_fp=*fp;
  set_regs(c,&input);
  fp->mxcsr=input.mxcsr;
#ifdef NATIVE_FP
  fp->cwd=fp_input.cw;fp->swd=fp_input.sw;fp->ftw=fp_input.tw;
  fp->fop=0;fp->rip=0;fp->rdp=0;
  for(int i=0;i<32;i++)fp->st[i]=fp_input.st[i];
#endif
  for(int i=0;i<32;i++){fp->xmm[2*i]=(u32)input.xmm[i];fp->xmm[2*i+1]=(u32)(input.xmm[i]>>32);}
  mark_sse(fp,u->flags);phase=1;return;
 }
 if(phase!=1 || sig==10)fail("unexpected signal outside instruction",sig);
 if(c->rip<0x20000 || c->rip>=0x21000)fail("signal outside instruction buffer",c->rip);
 observed=*c;observed_fp=*fp;observed_signal=sig;observed_code=info[2];
 /* Return to the suspended kill(SIGUSR1) call on the runner's original stack.
  * Keep the current kernel-generated xstate allocation and extension metadata. */
 u64 fpp=c->fpstate;*c=recovery;c->fpstate=fpp;u->flags|=6;
 fp->mxcsr=recovery_fp.mxcsr;
#ifdef NATIVE_FP
 fp->cwd=recovery_fp.cwd;fp->swd=recovery_fp.swd;fp->ftw=recovery_fp.ftw;
 fp->fop=recovery_fp.fop;fp->rip=recovery_fp.rip;fp->rdp=recovery_fp.rdp;
 for(int i=0;i<32;i++)fp->st[i]=recovery_fp.st[i];
#endif
 for(int i=0;i<64;i++)fp->xmm[i]=recovery_fp.xmm[i];
 mark_sse(fp,u->flags);phase=2;
}
static void execute(void) {
 long r=call(10,(long)code,4096,3,0,0,0);if(r<0)fail("mprotect RW",r);
 for(int i=0;i<4096;i++)code[i]=0xcc;
 if(input.code[0]<1 || input.code[0]>15)fail("bad instruction length",input.code[0]);
 for(int i=0;i<input.code[0];i++)code[256+i]=input.code[1+i];
 r=call(10,(long)code,4096,5,0,0,0);if(r<0)fail("mprotect RX",r);
 phase=0;r=call(62,pid,10,0,0,0,0);if(r<0)fail("kill self SIGUSR1",r);
 if(phase!=2)fail("instruction did not produce a signal",phase);
}
static void self_check(int tf) {
 input.code[0]=1;input.code[1]=0x90;input.flags=0xcd7|(tf?0x100:0);input.mxcsr=0x1f80;
 for(int k=0;k<16;k++)input.r[k]=compat?0xa1234500ull+k:0x13579abc01234500ull+k;
 input.r[4]=0x8800;
 for(int k=0;k<32;k++)input.xmm[k]=0x123456789abcdef0ull+k;
 execute();u64 r[16];get_regs(&observed,r);
 if(observed_signal!=5 || observed.trapno!=(tf?1:3) || observed.rip!=(tf?0x20101:0x20102) || observed.cs!=(compat?0x23:0x33))
  fail("NOP mode/IP/trap calibration",observed.rip);
 for(int k=0;k<(compat?8:16);k++)if(r[k]!=input.r[k])fail("NOP input GPR calibration",k);
 if((observed.flags&0xdd5)!=(input.flags&0xdd5))fail("NOP flags calibration",observed.flags);
 if(!compat
#ifdef NATIVE_FP
    || 1
#endif
 ) {
  if(observed_fp.mxcsr!=input.mxcsr)fail("NOP MXCSR calibration",observed_fp.mxcsr);
  for(int k=0;k<32;k++)if((observed_fp.xmm[2*k]|((u64)observed_fp.xmm[2*k+1]<<32))!=input.xmm[k])fail("NOP XMM calibration",k);
 }
#ifdef NATIVE_FP
 if(observed_fp.cwd!=fp_input.cw || observed_fp.swd!=fp_input.sw || observed_fp.ftw!=fp_input.tw)
  fail("NOP x87 control/status/tag calibration",observed_fp.swd);
 for(int i=0;i<8;i++)for(int j=0;j<3;j++) {
  u32 mask=j==2?0xffff:0xffffffff;
  if((observed_fp.st[4*i+j]&mask)!=(fp_input.st[4*i+j]&mask))fail("NOP x87 stack calibration",i);
 }
#endif
}
#ifdef NATIVE_MEMORY
/* Only this isolated 8 KiB arena is exposed to memory test instructions.
 * Missing pages are unmapped (not PROT_NONE), so Linux cannot lazily resolve
 * an access and the CPU reports a genuine not-present fault. */
static u8 *arena=(u8 *)0x10000;
static u8 initial[8192];
static int mapped[2];
static void writable(int page) {
 u8 *p=arena+page*4096;
 if(!mapped[page]) {
  long r=call(9,(long)p,4096,3,0x100022,-1,0); /* MAP_FIXED_NOREPLACE */
  if(r!=(long)p)fail("memory arena mapping",r);
  mapped[page]=1;
 } else {long r=call(10,(long)p,4096,3,0,0,0);if(r<0)fail("memory arena writable",r);}
}
static void memory_prepare(void) {
 for(int p=0;p<2;p++)writable(p);
 u32 seed=input.seed;
 for(int k=0;k<2048;k++) {
  seed^=seed<<13;seed^=seed>>17;seed^=seed<<5;
  ((u32 *)arena)[k]=seed;
 }
#ifdef NATIVE_FP
 memcpy(arena,fp_input.memory,64);
#endif
 memcpy(initial,arena,8192);
 for(int p=0;p<2;p++) {
  if(input.pte[p]==0) {
   long r=call(11,(long)(arena+p*4096),4096,0,0,0,0);
   if(r<0)fail("unmap data page",r);mapped[p]=0;
  } else if(input.pte[p]==0x65) {
   long r=call(10,(long)(arena+p*4096),4096,1,0,0,0);
   if(r<0)fail("read-only data page",r);
  } else if(input.pte[p]!=0x67)fail("unsupported data permission",input.pte[p]);
 }
}
static void memory_restore(void) {
 for(int p=0;p<2;p++) {
  int missing=!mapped[p];writable(p);
  /* An unmapped page cannot have changed. Restore its original bytes only;
   * never conceal partial stores in a page that was accessible. */
  if(missing)memcpy(arena+p*4096,initial+p*4096,4096);
 }
}
#ifdef NATIVE_FP
static u8 memory_byte(int i) {
 if(input.pad==1 && i<512) {
  int keep=i<5 || (i>=24 && i<28) || (i>=32 && i<160 && (i-32)%16<10) ||
           (i>=160 && i<288) || i>=464;
  if(!keep)return 0;
 }
 if((input.pad==2 || input.pad==3) && i<28 && !(i<2 || (i>=4 && i<6) || (i>=8 && i<10)))return 0;
 return arena[i];
}
#endif
static u32 memory_hash(void) {
 u32 h=2166136261u;for(int i=0;i<8192;i++)h=(h^
#ifdef NATIVE_FP
 memory_byte(i)
#else
 arena[i]
#endif
 )*16777619u;return h;
}
static u64 page_hash(int page) {
 u64 h=14695981039346656037ull;for(int i=0;i<4096;i++)h=(h^
#ifdef NATIVE_FP
 memory_byte(page*4096+i)
#else
 arena[page*4096+i]
#endif
 )*1099511628211ull;return h;
}
static void memory_check(void) {
 /* Flat user DS/ES are required for compatibility-mode data accesses.
  * This freestanding process has no TLS or libc segment dependencies. */
 __asm__ volatile("mov $0x2b,%%ax; mov %%ax,%%ds; mov %%ax,%%es":::"rax","memory");
 input.flags=0x202;input.seed=1;input.mxcsr=0x1f80;input.pte[0]=input.pte[1]=0x67;
 input.r[3]=0x10000;input.code[0]=2;input.code[1]=0x8b;input.code[2]=3;
 memory_prepare();execute();memory_restore();
 if(observed.trapno!=3 || observed.rax!=
#ifdef NATIVE_FP
    *(u32 *)fp_input.memory
#else
    0x42021
#endif
    || observed.rip!=0x20103)fail("memory load calibration",observed.trapno);
 input.r[0]=0x12345678;input.code[1]=0x89;
 memory_prepare();execute();memory_restore();
 if(observed.trapno!=3 || *(u32 *)arena!=0x12345678)fail("memory store calibration",observed.trapno);
 input.r[3]=0x11000;input.pte[1]=0x65;
 memory_prepare();execute();memory_restore();
 if(observed.trapno!=14 || observed.err!=7 || observed.cr2!=0x11000 || observed.rip!=0x20100 ||
    *(u32 *)(arena+4096)!=*(u32 *)(initial+4096))fail("read-only fault calibration",observed.err);
 input.pte[1]=0;input.code[1]=0x8b;
 memory_prepare();execute();memory_restore();
 if(observed.trapno!=14 || observed.err!=4 || observed.cr2!=0x11000 || observed.rax!=0x12345678)
  fail("unmapped fault calibration",observed.err);
 text(2,"PASS: memory load/store, read-only and unmapped fault calibration\n");
}
#endif
void start(u64 *stack) {
 if(stack[0]!=2){text(2,"usage: oracle i386|x86_64 < native.bin\n");finish(2);}
 const char *arch=(const char *)stack[2];compat=arch[0]=='i';
 u64 count;read_all(&count,8);if(!count || count>1000000)fail("invalid count",count);
 pid=call(39,0,0,0,0,0,0);
 long mapping=call(9,0x20000,4096,3,0x22,-1,0);if(mapping!=0x20000)fail("cannot map code at 0x20000",mapping);code=(u8 *)mapping;
 long alt=call(9,0,1024*1024,3,0x22,-1,0);if(alt<0)fail("alternate signal stack allocation",alt);
 struct stack ss={(u64)alt,0,0,1024*1024};long res=call(131,(long)&ss,0,0,0,0,0);if(res<0)fail("sigaltstack",res);
 struct action action={(u64)handler,0x0c000004,(u64)signal_restorer,~0ull};
 int signals[]={4,5,7,8,10,11};
 for(int k=0;k<6;k++){res=call(13,signals[k],(long)&action,0,8,0,0);if(res<0)fail("rt_sigaction",res);}
#ifdef NATIVE_FP
 if(!compat)fail("FP oracle requires i386 mode",0);
 /* Nonzero TOP and a mixture of empty/nonempty physical registers. */
 fp_input.cw=0x37f;fp_input.sw=0x2800;fp_input.tw=0xa5;
 for(int i=0;i<8;i++){fp_input.st[4*i]=i+1;fp_input.st[4*i+1]=0x80000000;fp_input.st[4*i+2]=0x3fff+i;}
#endif
 self_check(0);self_check(1);
 text(2,"PASS: NOP state calibration with TF off/on\n");
#ifdef NATIVE_MEMORY
 memory_check();
#endif
 text(1,"BEGIN ");hex(1,count);text(1,"\n");
 for(u64 index=0;index<count;index++) {
  read_all(&input,sizeof(input));
#ifdef NATIVE_FP
  read_all(&fp_input,sizeof(fp_input));
#endif
#ifdef NATIVE_MEMORY
  memory_prepare();
#endif
  execute();
#ifdef NATIVE_MEMORY
  memory_restore();
#endif
  hex(1,index);hex(1,observed_signal);hex(1,(u32)observed_code);hex(1,observed.rip);hex(1,observed.cs);hex(1,observed.flags);
  u64 r[16];get_regs(&observed,r);for(int k=0;k<16;k++)hex(1,r[k]);
  for(int k=0;k<32;k++)hex(1,observed_fp.xmm[2*k]|((u64)observed_fp.xmm[2*k+1]<<32));
  hex(1,observed_fp.mxcsr);hex(1,observed.trapno);hex(1,observed.err);hex(1,observed.cr2);
#ifdef NATIVE_MEMORY
  hex(1,memory_hash());hex(1,page_hash(0));hex(1,page_hash(1));
#endif
#ifdef NATIVE_FP
  hex(1,observed_fp.cwd);hex(1,observed_fp.swd);hex(1,observed_fp.ftw);
  hex(1,observed_fp.fop);hex(1,(u32)observed_fp.rip);hex(1,(u32)observed_fp.rdp);
  for(int i=0;i<8;i++) {
   hex(1,observed_fp.st[4*i]|((u64)observed_fp.st[4*i+1]<<32));
   hex(1,observed_fp.st[4*i+2]&0xffff);
  }
#endif
  text(1,"\n");
 }
 u8 extra;if(call(0,0,(long)&extra,1,0,0,0)!=0)fail("trailing input",0);
 text(1,"END\n");finish(0);
}
