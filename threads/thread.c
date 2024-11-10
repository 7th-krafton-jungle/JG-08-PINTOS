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
static struct list sleep_list;

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
void thread_sleep(int64_t ticks);
void thread_awake(int64_t ticks);
bool compare_wakeup_ticks(const struct list_elem *a, const struct list_elem *b, void *aux);
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
    list_init(&sleep_list);      // 잠든 목록 초기화
    list_init(&destruction_req); // 소멸 요청 목록 초기화

    /* Set up a thread structure for the running thread. */
    initial_thread = running_thread();                // 현재 실행 중인 스레드를 초기 스레드로 설정
    init_thread(initial_thread, "main", PRI_DEFAULT); // 초기 스레드 초기화
    initial_thread->status = THREAD_RUNNING;          // 초기 스레드 상태를 실행 중으로 설정
    initial_thread->tid = allocate_tid();             // 초기 스레드 ID 할당
}

/* 선점형 스레드 스케줄링을 시작하고 아이들 스레드를 생성합니다. */
void thread_start(void) {
    /* 아이들 스레드 생성 */
    struct semaphore idle_started;
    sema_init(&idle_started, 0);                         // 아이들 스레드 시작 세마포어 초기화
    thread_create("idle", PRI_MIN, idle, &idle_started); // 아이들 스레드 생성

    /* 선점형 스레드 스케줄링 시작 */
    intr_enable(); // 인터럽트 활성화

    /* 아이들 스레드가 idle_thread를 초기화할 때까지 대기 */
    sema_down(&idle_started);
}

/* 타이머 인터럽트 핸들러에 의해 각 타이머 틱마다 호출됩니다.
   따라서 이 함수는 외부 인터럽트 컨텍스트에서 실행됩니다.

   이 함수는 현재 실행 중인 스레드의 통계를 업데이트하고
   스레드의 실행 시간이 TIME_SLICE를 초과하면 스레드를 선점합니다.
   idle_ticks, kernel_ticks, user_ticks 등의 통계를 관리하여
   시스템의 스레드 실행 현황을 모니터링합니다. */
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

/* NAME이라는 이름과 주어진 초기 PRIORITY를 가진 새로운 커널 스레드를 생성합니다.
   이 스레드는 FUNCTION을 실행하며 AUX를 인자로 전달하고, ready 큐에 추가됩니다.
   생성된 새 스레드의 식별자를 반환하며, 생성에 실패하면 TID_ERROR를 반환합니다.

   thread_start()가 호출된 경우, 새 스레드는 thread_create()가 반환되기 전에
   스케줄될 수 있습니다. 심지어 thread_create()가 반환되기 전에 종료될 수도 있습니다.
   반대로 원래 스레드는 새 스레드가 스케줄되기 전에 임의의 시간 동안 실행될 수 있습니다.
   순서를 보장해야 하는 경우 세마포어나 다른 형태의 동기화를 사용하세요.

   제공된 코드는 새 스레드의 'priority' 멤버를 PRIORITY로 설정하지만,
   실제 우선순위 스케줄링은 구현되어 있지 않습니다.
   우선순위 스케줄링은 Problem 1-3의 목표입니다. */
tid_t thread_create(const char *name, int priority, thread_func *function, void *aux) {
    struct thread *t; // 스레드 포인터
    tid_t tid;        // 스레드 ID

    ASSERT(function != NULL); // 함수가 NULL이 아닌지 확인

    /* Allocate thread. */
    t = palloc_get_page(PAL_ZERO); // 페이지 할당
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
    thread_unblock(t);   // 스레드를 준비 목록에 추가
    thread_preemption(); // 선점 테스트 함수 호출

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

/* 차단된 스레드 T를 실행 가능한(ready-to-run) 상태로 전환하고 ready_list에 추가합니다.
   이 함수는 스레드 T가 차단된(blocked) 상태가 아닌 경우 오류가 발생합니다.
   (실행 중인 스레드를 ready 상태로 만들려면 thread_yield()를 사용하세요.)

   스레드를 ready_list에 추가할 때는 우선순위에 따라 정렬된 상태로 삽입됩니다.
   이는 compare_priority() 함수를 사용하여 수행되며, 우선순위가 높은 스레드가
   리스트의 앞쪽에 위치하게 됩니다.

   이 함수는 현재 실행 중인 스레드를 선점(preempt)하지 않으며, 인터럽트를 비활성화한
   상태에서 동작합니다. 이는 스레드의 상태 변경과 ready_list 삽입이 원자적으로
   수행되어야 하기 때문입니다. 함수 종료 시 이전 인터럽트 상태로 복원됩니다. */
void thread_unblock(struct thread *t) {
    enum intr_level old_level;

    ASSERT(is_thread(t));                // 스레드가 유효한지 확인
    old_level = intr_disable();          // 인터럽트 비활성화
    ASSERT(t->status == THREAD_BLOCKED); // 스레드 상태가 차단된 상태인지 확인

    list_insert_ordered(&ready_list, &t->elem, cmp_thread_priority, NULL); // 우선순위에 따라 정렬된 상태로 삽입

    t->status = THREAD_READY;  // 스레드 상태를 준비 상태로 설정
    intr_set_level(old_level); // 이전 인터럽트 레벨 복원
}

/* Returns the name of the running thread. */
const char *thread_name(void) { return thread_current()->name; }

/* 현재 실행 중인 스레드를 반환합니다.
   이 함수는 running_thread() 함수에 몇 가지 안전성 검사를 추가한 것입니다.
   자세한 내용은 thread.h 파일 상단의 큰 주석을 참조하세요. */
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
        /* 우선순위 순서대로 정렬된 상태를 유지하기 위해 list_insert_ordered() 사용
         * list_push_back()은 O(1)이지만 정렬되지 않은 상태로 삽입되어 스케줄링 시 우선순위 확인에 O(n) 소요
         * list_insert_ordered()는 삽입 시 O(n)이 소요되지만 정렬된 상태를 유지하여 스케줄링 성능 향상 */
        list_insert_ordered(&ready_list, &curr->elem, cmp_thread_priority, NULL);

    do_schedule(THREAD_READY); // 스케줄러 실행
    intr_set_level(old_level); // 이전 인터럽트 레벨 복원
}

/* 두 요소의 우선순위를 비교하는 함수
   우선순위가 높은 스레드가 먼저 실행되도록 함 */
bool cmp_thread_priority(const struct list_elem *a, const struct list_elem *b, void *aux) {
    return list_entry(a, struct thread, elem)->priority > list_entry(b, struct thread, elem)->priority;
}

/* 현재 스레드의 우선순위를 NEW_PRIORITY로 설정합니다. */
void thread_set_priority(int new_priority) {
    thread_current()->priority = new_priority; // 현재 스레드의 우선순위를 새로운 우선순위로 설정
    update_priority_for_donations();           // 우선순위 갱신
    preempt_priority();                        // 우선순위 선점 스케줄링
}

/* 현재 스레드의 우선순위를 반환합니다. */
int thread_get_priority(void) { return thread_current()->priority; }

/* 선점 테스트 함수
   현재 스레드의 우선순위가 ready_list의 맨 앞에 있는 스레드의 우선순위보다 낮으면
   선점을 위해 스레드를 양보합니다. */
void thread_preemption(void) {
    if (thread_current() == idle_thread) // 유휴 스레드면 종료
        return;
    if (list_empty(&ready_list)) // ready_list가 비어있으면 종료
        return;
    struct thread *curr = thread_current();                                          // 현재 실행중인 스레드
    struct thread *ready = list_entry(list_front(&ready_list), struct thread, elem); // ready_list의 맨 앞에 있는 스레드
    if (curr->priority < ready->priority) // ready_list에 현재 실행중인 스레드보다 우선순위가 높은 스레드가 있으면
        thread_yield();                   // 선점을 위해 스레드를 양보
}

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

/* 유휴 스레드. 실행 가능한 다른 스레드가 없을 때 실행됩니다.

   유휴 스레드는 처음에 thread_start()에 의해 ready_list에 추가됩니다.
   최초 한 번 스케줄링되어 idle_thread를 초기화하고, thread_start()가
   계속 실행될 수 있도록 전달받은 세마포어를 "up"한 다음 즉시 블록됩니다.
   그 이후로는 유휴 스레드가 ready_list에 나타나지 않습니다.
   ready_list가 비어있을 때 next_thread_to_run()에서 특별한 경우로
   반환됩니다. */
static void idle(void *idle_started_ UNUSED) {
    struct semaphore *idle_started = idle_started_;

    idle_thread = thread_current();
    sema_up(idle_started);

    for (;;) {
        /* 다른 스레드를 실행하도록 허용합니다. */
        intr_disable();
        thread_block();

        /* 인터럽트를 다시 활성화하고 다음 인터럽트를 기다립니다.

           'sti' 명령어는 다음 명령어가 완료될 때까지 인터럽트를 비활성화하므로,
           이 두 명령어는 원자적으로 실행됩니다. 이러한 원자성은 매우 중요합니다.
           만약 그렇지 않다면, 인터럽트를 다시 활성화한 후 다음 인터럽트가
           발생하기를 기다리는 사이에 인터럽트가 처리될 수 있어서
           최대 한 클록 틱만큼의 시간이 낭비될 수 있기 때문입니다.

           참고: [IA32-v2a] "HLT", [IA32-v2b] "STI", [IA32-v3a]
           7.11.1 "HLT Instruction" */
        asm volatile("sti; hlt" : : : "memory");
    }
}

/* 커널 스레드 함수
   새로 생성된 스레드가 실행할 함수와 인자를 받아 실제 스레드의 실행을 시작합니다.
   이 함수는 thread_create()에서 생성된 스레드의 시작점이 되며,
   다음과 같은 작업을 수행합니다:
   1. 인터럽트를 활성화하여 스레드가 인터럽트를 처리할 수 있도록 합니다.
   2. 전달받은 스레드 함수를 실행합니다.
   3. 스레드 함수가 반환되면 thread_exit()을 호출하여 스레드를 종료합니다.

   이 함수는 스레드의 컨텍스트에서 실행되며, thread_create()에서 설정한
   스택과 레지스터 상태를 이용하여 새로운 실행 환경을 구성합니다. */
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
    t->init_priority = priority;                       // 초기 우선순위 설정
    t->wait_on_lock = NULL;                            // 대기 중인 잠금 설정
    list_init(&t->donations);                          // 기부 목록 초기화
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

/* 현재 실행 중인 스레드를 잠들게 하고, 일정 시간 후에 깨어나도록 합니다.
   이 함수는 timer_sleep() 함수에서 호출되며, busy waiting을 방지하기 위해 사용됩니다.
   스레드를 sleep_list에 삽입하고 THREAD_BLOCKED 상태로 변경합니다.
   sleep_list는 깨어날 시간(wakeup_ticks) 순으로 정렬되어 있으며,
   매 타이머 틱마다 thread_awake() 함수가 호출되어 깨어날 시간이 된 스레드들을 깨웁니다.
   인터럽트를 비활성화하여 race condition을 방지하고,
   idle 스레드는 절대 잠들지 않도록 보장합니다. */
void thread_sleep(int64_t ticks) {
    struct thread *cur = thread_current();      // 현재 실행 중인 스레드
    enum intr_level old_level = intr_disable(); // 이전 인터럽트 레벨

    ASSERT(cur != idle_thread); // 현재 실행 중인 스레드가 idle_thread가 아닌지 확인

    cur->wakeup_ticks = ticks;                                                // 일어날 시간을 저장
    list_insert_ordered(&sleep_list, &cur->elem, compare_wakeup_ticks, NULL); // sleep_list 에 추가
    thread_block();                                                           // block 상태로 변경

    intr_set_level(old_level); // 인터럽트 레벨 복원
}

/* sleep_list를 wakeup_ticks 기준으로 정렬하기 위한 비교 함수 */
bool compare_wakeup_ticks(const struct list_elem *a, const struct list_elem *b, void *aux) {
    const struct thread *t1 = list_entry(a, struct thread, elem); // 스레드 1
    const struct thread *t2 = list_entry(b, struct thread, elem); // 스레드 2
    return t1->wakeup_ticks < t2->wakeup_ticks; // 스레드 1의 깨어날 시간이 스레드 2의 깨어날 시간보다 작은지 확인
}

/* 현재 시간(ticks)이 되어 깨어나야 할 스레드들을 깨웁니다.
   sleep_list에서 깨어날 시간(wakeup_ticks)이 현재 시간보다 작거나 같은 스레드들을 찾아
   리스트에서 제거하고 THREAD_READY 상태로 변경합니다.
   sleep_list는 wakeup_ticks 기준으로 오름차순 정렬되어 있으므로,
   더 이상 깨워야 할 스레드가 없다고 판단되면 순회를 중단합니다.
   이 함수는 매 타이머 인터럽트마다 호출되며, race condition 방지를 위해
   인터럽트를 비활성화한 상태에서 동작합니다. */
void thread_awake(int64_t ticks) {
    struct list_elem *e = list_begin(&sleep_list); // sleep_list 의 첫 번째 요소
    enum intr_level old_level = intr_disable();    // 인터럽트 off

    while (e != list_end(&sleep_list)) {
        struct thread *thr = list_entry(e, struct thread, elem); // 스레드

        if (thr->wakeup_ticks <= ticks) {
            e = list_remove(e);  // 스레드 제거
            thread_unblock(thr); // 스레드 활성화
            preempt_priority();  // 우선순위 선점 스케줄링
        } else
            break;
    }
    intr_set_level(old_level); // 인터럽트 레벨 복원
}

/* Returns a tid to use for a new thread. */
static tid_t allocate_tid(void) {
    static tid_t next_tid = 1; // 다음에 할당할 스레드 ID
    tid_t tid;                 // 할당된 스레드 ID

    lock_acquire(&tid_lock); // 잠금 획득
    tid = next_tid++;        // 다음에 할당할 스레드 ID 증가
    lock_release(&tid_lock); // 잠금 해제

    return tid; // 할당된 스레드 ID 반환
}

/* 우선순위 선점 스케줄링 */
void preempt_priority(void) {
    if (thread_current() == idle_thread) // 현재 실행중인 스레드가 idle_thread라면 바로 반환
        return;
    if (list_empty(&ready_list)) // ready_list가 비어있다면 바로 반환
        return;
    struct thread *curr = thread_current();                                          // 현재 실행중인 스레드
    struct thread *ready = list_entry(list_front(&ready_list), struct thread, elem); // ready_list의 첫 번째 요소F
    if (curr->priority < ready->priority) // ready_list에 현재 실행중인 스레드보다 우선순위가 높은 스레드가 있으면
        thread_yield();                   // 스레드 양보
}
