#include "threads/thread.h"
#include "intrinsic.h"
#include "threads/flags.h"
#include "threads/interrupt.h"
#include "threads/intr-stubs.h"
#include "threads/palloc.h"
#include "threads/synch.h"
#include "threads/vaddr.h"
#include <debug.h>
#include <random.h>
#include <stddef.h>
#include <stdio.h>
#include <string.h>
#ifdef USERPROG
#include "userprog/process.h"
#endif

/* Random value for struct thread's `magic' member.
   Used to detect stack overflow.  See the big comment at the top
   of thread.h for details. */
#define THREAD_MAGIC 0xcd6abf4b

/* Random value for basic thread
   Do not modify this value. */
#define THREAD_BASIC 0xd42df210

/* List of processes in THREAD_READY state, that is, processes
   that are ready to run but not actually running. */
static struct list ready_list;

/* Idle thread. */
static struct thread *idle_thread;

/* Initial thread, the thread running init.c:main(). */
static struct thread *initial_thread;

/* Lock used by allocate_tid(). */
static struct lock tid_lock;

/* Thread destruction requests */
static struct list destruction_req;

/* Statistics. */
static long long idle_ticks;   /* # of timer ticks spent idle. */
static long long kernel_ticks; /* # of timer ticks in kernel threads. */
static long long user_ticks;   /* # of timer ticks in user programs. */

/* Scheduling. */
#define TIME_SLICE 4          /* # of timer ticks to give each thread. */
static unsigned thread_ticks; /* # of timer ticks since last yield. */

/* If false (default), use round-robin scheduler.
   If true, use multi-level feedback queue scheduler.
   Controlled by kernel command-line option "-o mlfqs". */
bool thread_mlfqs;

static void kernel_thread(thread_func *, void *aux);

static void idle(void *aux UNUSED);
static struct thread *next_thread_to_run(void);
static void init_thread(struct thread *, const char *name, int priority);
static void do_schedule(int status);
static void schedule(void);
static tid_t allocate_tid(void);

/* Returns true if T appears to point to a valid thread. */
#define is_thread(t) ((t) != NULL && (t)->magic == THREAD_MAGIC)

/* Returns the running thread.
 * Read the CPU's stack pointer `rsp', and then round that
 * down to the start of a page.  Since `struct thread' is
 * always at the beginning of a page and the stack pointer is
 * somewhere in the middle, this locates the curent thread. */
#define running_thread() ((struct thread *)(pg_round_down(rrsp())))

// Global descriptor table for the thread_start.
// Because the gdt will be setup after the thread_init, we should
// setup temporal gdt first.
static uint64_t gdt[3] = {0, 0x00af9a000000ffff, 0x00cf92000000ffff};

/* Initializes the threading system by transforming the code
   that's currently running into a thread.  This can't work in
   general and it is possible in this case only because loader.S
   was careful to put the bottom of the stack at a page boundary.

   Also initializes the run queue and the tid lock.

   After calling this function, be sure to initialize the page
   allocator before trying to create any threads with
   thread_create().

   It is not safe to call thread_current() until this function
   finishes. */
void thread_init(void) {
    ASSERT(intr_get_level() == INTR_OFF); // 인터럽트가 비활성화되어 있는지 확인

    /* Reload the temporal gdt for the kernel
     * This gdt does not include the user context.
     * The kernel will rebuild the gdt with user context, in gdt_init (). */
    struct desc_ptr gdt_ds = {.size = sizeof(gdt) - 1, .address = (uint64_t)gdt};
    lgdt(&gdt_ds); // GDT 로드

    /* Init the globla thread context */
    lock_init(&tid_lock);        // 스레드 ID 잠금 초기화
    list_init(&ready_list);      // 준비 목록 초기화
    list_init(&destruction_req); // 소멸 요청 목록 초기화

    /* Set up a thread structure for the running thread. */
    initial_thread = running_thread();                // 현재 실행 중인 스레드를 초기 스레드로 설정
    init_thread(initial_thread, "main", PRI_DEFAULT); // 초기 스레드 초기화
    initial_thread->status = THREAD_RUNNING;          // 초기 스레드 상태를 실행 중으로 설정
    initial_thread->tid = allocate_tid();             // 초기 스레드 ID 할당
}

/* Starts preemptive thread scheduling by enabling interrupts.
   Also creates the idle thread. */
void thread_start(void) {
    /* Create the idle thread. */
    struct semaphore idle_started;
    sema_init(&idle_started, 0);                         // 아이들 스레드 시작 세마포어 초기화
    thread_create("idle", PRI_MIN, idle, &idle_started); // 아이들 스레드 생성

    /* Start preemptive thread scheduling. */
    intr_enable(); // 인터럽트 활성화

    /* Wait for the idle thread to initialize idle_thread. */
    sema_down(&idle_started); // 아이들 스레드가 idle_thread를 초기화할 때까지 대기
}

/* Called by the timer interrupt handler at each timer tick.
   Thus, this function runs in an external interrupt context. */
void thread_tick(void) {
    struct thread *t = thread_current(); // 현재 실행 중인 스레드 가져오기

    /* Update statistics. */
    if (t == idle_thread)
        idle_ticks++; // 아이들 스레드의 틱 수 증가
#ifdef USERPROG
    else if (t->pml4 != NULL)
        user_ticks++; // 사용자 스레드의 틱 수 증가
#endif
    else
        kernel_ticks++; // 커널 스레드의 틱 수 증가

    /* Enforce preemption. */
    if (++thread_ticks >= TIME_SLICE)
        intr_yield_on_return(); // 틱 수가 TIME_SLICE를 초과하면 인터럽트 양보
}

/* Prints thread statistics. */
void thread_print_stats(void) {
    printf("Thread: %lld idle ticks, %lld kernel ticks, %lld user ticks\n", idle_ticks, kernel_ticks, user_ticks);
}

/* Creates a new kernel thread named NAME with the given initial
   PRIORITY, which executes FUNCTION passing AUX as the argument,
   and adds it to the ready queue.  Returns the thread identifier
   for the new thread, or TID_ERROR if creation fails.

   If thread_start() has been called, then the new thread may be
   scheduled before thread_create() returns.  It could even exit
   before thread_create() returns.  Contrariwise, the original
   thread may run for any amount of time before the new thread is
   scheduled.  Use a semaphore or some other form of
   synchronization if you need to ensure ordering.

   The code provided sets the new thread's `priority' member to
   PRIORITY, but no actual priority scheduling is implemented.
   Priority scheduling is the goal of Problem 1-3. */
tid_t thread_create(const char *name, int priority, thread_func *function, void *aux) {
    struct thread *t; // 스레드 포인터
    tid_t tid;        // 스레드 ID

    ASSERT(function != NULL); // 함수가 NULL이 아닌지 확인

    /* Allocate thread. */
    t = palloc_get_page(PAL_ZERO);
    if (t == NULL)
        return TID_ERROR; // 메모리 할당 실패 시 TID_ERROR 반환

    /* Initialize thread. */
    init_thread(t, name, priority); // 스레드 초기화
    tid = t->tid = allocate_tid();  // 스레드 ID 할당

    /* Call the kernel_thread if it scheduled.
     * Note) rdi is 1st argument, and rsi is 2nd argument. */
    t->tf.rip = (uintptr_t)kernel_thread; // 커널 스레드 함수 주소 설정
    t->tf.R.rdi = (uint64_t)function;     // 함수 인수 설정
    t->tf.R.rsi = (uint64_t)aux;          // 함수 인수 설정
    t->tf.ds = SEL_KDSEG;                 // 데이터 세그먼트 선택자 설정
    t->tf.es = SEL_KDSEG;                 // 데이터 세그먼트 선택자 설정
    t->tf.ss = SEL_KDSEG;                 // 데이터 세그먼트 선택자 설정
    t->tf.cs = SEL_KCSEG;                 // 코드 세그먼트 선택자 설정
    t->tf.eflags = FLAG_IF;               // 플래그 설정

    /* Add to run queue. */
    thread_unblock(t); // 스레드를 준비 목록에 추가

    return tid; // 스레드 ID 반환
}

/* Puts the current thread to sleep.  It will not be scheduled
   again until awoken by thread_unblock().

   This function must be called with interrupts turned off.  It
   is usually a better idea to use one of the synchronization
   primitives in synch.h. */
void thread_block(void) {
    ASSERT(!intr_context());
    ASSERT(intr_get_level() == INTR_OFF);
    thread_current()->status = THREAD_BLOCKED;
    schedule();
}

/* Transitions a blocked thread T to the ready-to-run state.
   This is an error if T is not blocked.  (Use thread_yield() to
   make the running thread ready.)

   This function does not preempt the running thread.  This can
   be important: if the caller had disabled interrupts itself,
   it may expect that it can atomically unblock a thread and
   update other data. */
void thread_unblock(struct thread *t) {
    enum intr_level old_level;

    ASSERT(is_thread(t));

    old_level = intr_disable();
    ASSERT(t->status == THREAD_BLOCKED);
    list_push_back(&ready_list, &t->elem);
    t->status = THREAD_READY;
    intr_set_level(old_level);
}

/* Returns the name of the running thread. */
const char *thread_name(void) { return thread_current()->name; }

/* Returns the running thread.
   This is running_thread() plus a couple of sanity checks.
   See the big comment at the top of thread.h for details. */
struct thread *thread_current(void) {
    struct thread *t = running_thread();

    /* Make sure T is really a thread.
       If either of these assertions fire, then your thread may
       have overflowed its stack.  Each thread has less than 4 kB
       of stack, so a few big automatic arrays or moderate
       recursion can cause stack overflow. */
    ASSERT(is_thread(t));
    ASSERT(t->status == THREAD_RUNNING);

    return t;
}

/* Returns the running thread's tid. */
tid_t thread_tid(void) { return thread_current()->tid; }

/* Deschedules the current thread and destroys it.  Never
   returns to the caller. */
void thread_exit(void) {
    ASSERT(!intr_context());

#ifdef USERPROG
    process_exit();
#endif

    /* Just set our status to dying and schedule another process.
       We will be destroyed during the call to schedule_tail(). */
    intr_disable();
    do_schedule(THREAD_DYING);
    NOT_REACHED();
}

/* CPU를 양보합니다. 현재 스레드는 슬립 상태가 되지 않으며
   스케줄러의 판단에 따라 즉시 다시 스케줄링될 수 있습니다. */
void thread_yield(void) {
    struct thread *curr = thread_current(); // 현재 실행 중인 스레드 가져오기
    enum intr_level old_level;              // 이전 인터럽트 레벨 저장

    ASSERT(!intr_context());

    old_level = intr_disable(); // 인터럽트 비활성화
    if (curr != idle_thread)
        list_push_back(&ready_list,
                       &curr->elem); // 현재 스레드를 준비 목록에 추가
    do_schedule(THREAD_READY);       // 스케줄러 실행
    intr_set_level(old_level);       // 이전 인터럽트 레벨 복원
}

/* Sets the current thread's priority to NEW_PRIORITY. */
void thread_set_priority(int new_priority) { thread_current()->priority = new_priority; }

/* Returns the current thread's priority. */
int thread_get_priority(void) { return thread_current()->priority; }

/* Sets the current thread's nice value to NICE. */
void thread_set_nice(int nice UNUSED) { /* TODO: Your implementation goes here */ }

/* Returns the current thread's nice value. */
int thread_get_nice(void) {
    /* TODO: Your implementation goes here */
    return 0;
}

/* Returns 100 times the system load average. */
int thread_get_load_avg(void) {
    /* TODO: Your implementation goes here */
    return 0;
}

/* Returns 100 times the current thread's recent_cpu value. */
int thread_get_recent_cpu(void) {
    /* TODO: Your implementation goes here */
    return 0;
}

/* Idle thread.  Executes when no other thread is ready to run.

   The idle thread is initially put on the ready list by
   thread_start().  It will be scheduled once initially, at which
   point it initializes idle_thread, "up"s the semaphore passed
   to it to enable thread_start() to continue, and immediately
   blocks.  After that, the idle thread never appears in the
   ready list.  It is returned by next_thread_to_run() as a
   special case when the ready list is empty. */
static void idle(void *idle_started_ UNUSED) {
    struct semaphore *idle_started = idle_started_;

    idle_thread = thread_current();
    sema_up(idle_started);

    for (;;) {
        /* Let someone else run. */
        intr_disable();
        thread_block();

        /* Re-enable interrupts and wait for the next one.

           The `sti' instruction disables interrupts until the
           completion of the next instruction, so these two
           instructions are executed atomically.  This atomicity is
           important; otherwise, an interrupt could be handled
           between re-enabling interrupts and waiting for the next
           one to occur, wasting as much as one clock tick worth of
           time.

           See [IA32-v2a] "HLT", [IA32-v2b] "STI", and [IA32-v3a]
           7.11.1 "HLT Instruction". */
        asm volatile("sti; hlt" : : : "memory");
    }
}

/* Function used as the basis for a kernel thread. */
static void kernel_thread(thread_func *function, void *aux) {
    ASSERT(function != NULL); // 함수가 NULL이 아닌지 확인

    intr_enable(); /* 인터럽트 활성화 */
    function(aux); /* 스레드 함수 실행 */
    thread_exit(); /* 함수가 반환하면 스레드 종료 */
}

/* Does basic initialization of T as a blocked thread named
   NAME. */
static void init_thread(struct thread *t, const char *name, int priority) {
    ASSERT(t != NULL);                                  // 스레드가 NULL이 아닌지 확인
    ASSERT(PRI_MIN <= priority && priority <= PRI_MAX); // 우선순위가 유효한 범위 내에 있는지 확인
    ASSERT(name != NULL);                               // 이름이 NULL이 아닌지 확인

    memset(t, 0, sizeof *t);                           // 스레드 초기화
    t->status = THREAD_BLOCKED;                        // 스레드 상태 설정
    strlcpy(t->name, name, sizeof t->name);            // 스레드 이름 설정
    t->tf.rsp = (uint64_t)t + PGSIZE - sizeof(void *); // 스레드 스택 포인터 설정
    t->priority = priority;                            // 스레드 우선순위 설정
    t->magic = THREAD_MAGIC;                           // 스레드 매직 넘버 설정
}

/* Chooses and returns the next thread to be scheduled.  Should
   return a thread from the run queue, unless the run queue is
   empty.  (If the running thread can continue running, then it
   will be in the run queue.)  If the run queue is empty, return
   idle_thread. */
static struct thread *next_thread_to_run(void) {
    if (list_empty(&ready_list))
        return idle_thread;
    else
        return list_entry(list_pop_front(&ready_list), struct thread, elem);
}

/* Use iretq to launch the thread */
void do_iret(struct intr_frame *tf) {
    __asm __volatile("movq %0, %%rsp\n"
                     "movq 0(%%rsp),%%r15\n"
                     "movq 8(%%rsp),%%r14\n"
                     "movq 16(%%rsp),%%r13\n"
                     "movq 24(%%rsp),%%r12\n"
                     "movq 32(%%rsp),%%r11\n"
                     "movq 40(%%rsp),%%r10\n"
                     "movq 48(%%rsp),%%r9\n"
                     "movq 56(%%rsp),%%r8\n"
                     "movq 64(%%rsp),%%rsi\n"
                     "movq 72(%%rsp),%%rdi\n"
                     "movq 80(%%rsp),%%rbp\n"
                     "movq 88(%%rsp),%%rdx\n"
                     "movq 96(%%rsp),%%rcx\n"
                     "movq 104(%%rsp),%%rbx\n"
                     "movq 112(%%rsp),%%rax\n"
                     "addq $120,%%rsp\n"
                     "movw 8(%%rsp),%%ds\n"
                     "movw (%%rsp),%%es\n"
                     "addq $32, %%rsp\n"
                     "iretq"
                     :
                     : "g"((uint64_t)tf)
                     : "memory");
}

/* 새로운 스레드의 페이지 테이블을 활성화하고, 이전 스레드가 종료되는 경우
   해당 스레드를 제거하여 스레드를 전환합니다.

   이 함수가 호출될 때는 이미 이전 스레드(PREV)에서 전환이 이루어졌고,
   새로운 스레드가 실행 중이며, 인터럽트는 여전히 비활성화된 상태입니다.

   스레드 전환이 완료될 때까지 printf()를 호출하는 것은 안전하지 않습니다.
   실제로 이는 printf()가 함수의 마지막에 추가되어야 함을 의미합니다. */
static void thread_launch(struct thread *th) {
    uint64_t tf_cur = (uint64_t)&running_thread()->tf;
    uint64_t tf = (uint64_t)&th->tf;
    ASSERT(intr_get_level() == INTR_OFF);

    /* 주요 스위칭 로직
     * 먼저 전체 실행 컨텍스트를 intr_frame으로 복원한 다음
     * do_iret을 호출하여 다음 스레드로 전환합니다.
     * 주의: 스위칭이 완료될 때까지 여기서부터는
     * 스택을 사용해서는 안 됩니다. */
    __asm __volatile(
        /* Store registers that will be used. */
        "push %%rax\n"
        "push %%rbx\n"
        "push %%rcx\n"
        /* Fetch input once */
        "movq %0, %%rax\n"
        "movq %1, %%rcx\n"
        "movq %%r15, 0(%%rax)\n"
        "movq %%r14, 8(%%rax)\n"
        "movq %%r13, 16(%%rax)\n"
        "movq %%r12, 24(%%rax)\n"
        "movq %%r11, 32(%%rax)\n"
        "movq %%r10, 40(%%rax)\n"
        "movq %%r9, 48(%%rax)\n"
        "movq %%r8, 56(%%rax)\n"
        "movq %%rsi, 64(%%rax)\n"
        "movq %%rdi, 72(%%rax)\n"
        "movq %%rbp, 80(%%rax)\n"
        "movq %%rdx, 88(%%rax)\n"
        "pop %%rbx\n" // Saved rcx
        "movq %%rbx, 96(%%rax)\n"
        "pop %%rbx\n" // Saved rbx
        "movq %%rbx, 104(%%rax)\n"
        "pop %%rbx\n" // Saved rax
        "movq %%rbx, 112(%%rax)\n"
        "addq $120, %%rax\n"
        "movw %%es, (%%rax)\n"
        "movw %%ds, 8(%%rax)\n"
        "addq $32, %%rax\n"
        "call __next\n" // read the current rip.
        "__next:\n"
        "pop %%rbx\n"
        "addq $(out_iret -  __next), %%rbx\n"
        "movq %%rbx, 0(%%rax)\n" // rip
        "movw %%cs, 8(%%rax)\n"  // cs
        "pushfq\n"
        "popq %%rbx\n"
        "mov %%rbx, 16(%%rax)\n" // eflags
        "mov %%rsp, 24(%%rax)\n" // rsp
        "movw %%ss, 32(%%rax)\n"
        "mov %%rcx, %%rdi\n"
        "call do_iret\n"
        "out_iret:\n"
        :
        : "g"(tf_cur), "g"(tf)
        : "memory");
}

/* 새로운 프로세스를 스케줄링합니다. 진입 시 인터럽트가 꺼져있어야 합니다.
 * 이 함수는 현재 스레드의 상태를 주어진 상태로 변경하고
 * 다음에 실행할 다른 스레드를 찾아 전환합니다.
 * schedule() 함수 내에서 printf()를 호출하는 것은 안전하지 않습니다. */
static void do_schedule(int status) {
    ASSERT(intr_get_level() == INTR_OFF);
    ASSERT(thread_current()->status == THREAD_RUNNING);
    while (!list_empty(&destruction_req)) {
        struct thread *victim = list_entry(list_pop_front(&destruction_req), struct thread, elem);
        palloc_free_page(victim);
    }
    thread_current()->status = status;
    schedule();
}

/*
스케줄러 함수
주로 thread_yield(), thread_block(), thread_exit() 등의 함수 마지막 부분에
실행되며 CPU의 소유권을 현재 실행중인 스레드에서 다음에 실행될 스레드로 넘겨주는 작업을 진행한다.
cur는 현재 실행중인 스레드를, next는 다음에 실행될 스레드를 가리킨다.

next_thread_to_run 함수는 준비 목록에서 다음에 실행될 스레드를 선택하는 함수이다.
준비 목록이 비어있으면 idle_thread를 반환한다.
*/
static void schedule(void) {
    struct thread *curr = running_thread();     // 현재 실행중인 스레드 가져오기
    struct thread *next = next_thread_to_run(); // 다음에 실행될 스레드 가져오기

    ASSERT(intr_get_level() == INTR_OFF);
    ASSERT(curr->status != THREAD_RUNNING); // 현재 실행중인 스레드가 실행중이 아닌지 확인
    ASSERT(is_thread(next));                // 다음에 실행될 스레드가 스레드인지 확인
    /* Mark us as running. */
    next->status = THREAD_RUNNING; // 다음에 실행될 스레드를 실행중으로 설정

    /* Start new time slice. */
    thread_ticks = 0; // 시간 슬라이스 초기화

#ifdef USERPROG
    /* Activate the new address space. */
    process_activate(next); // 새로운 주소 공간 활성화
#endif

    if (curr != next) {
        /* 전환된 스레드가 종료 중이라면 해당 스레드의 구조체를 제거합니다.
           이 작업은 thread_exit()가 자기 자신의 기반을 무너뜨리지 않도록 늦게 수행되어야 합니다.
           현재 스택에서 페이지가 사용 중이므로 여기서는 페이지 해제 요청만 큐에 넣습니다.
           실제 제거 로직은 schedule() 함수의 시작 부분에서 호출됩니다. */
        if (curr && curr->status == THREAD_DYING && curr != initial_thread) {
            ASSERT(curr != next);
            list_push_back(&destruction_req, &curr->elem); // 소멸 요청 목록에 현재 스레드 추가
        }

        /* Before switching the thread, we first save the information
         * of current running. */
        thread_launch(next); // 스레드 전환
    }
}

/* Returns a tid to use for a new thread. */
static tid_t allocate_tid(void) {
    static tid_t next_tid = 1;
    tid_t tid;

    lock_acquire(&tid_lock);
    tid = next_tid++;
    lock_release(&tid_lock);

    return tid;
}
