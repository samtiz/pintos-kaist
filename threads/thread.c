#include "threads/thread.h"
#include <debug.h>
#include <stddef.h>
#include <random.h>
#include <stdio.h>
#include <string.h>
#include "threads/flags.h"
#include "threads/interrupt.h"
#include "threads/intr-stubs.h"
#include "threads/palloc.h"
#include "threads/synch.h"
#include "threads/vaddr.h"
#include "intrinsic.h"
/*modify-mlfqs*/
#include "devices/timer.h"
#include "threads/fixed_point.h"
/*modify-mlfqs*/
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


// [modify-alarmclock]
static struct list sleep_list;
int64_t min_sleep_tick;
// [modify-alarmclock]

/* Idle thread. */
static struct thread *idle_thread;

/* Initial thread, the thread running init.c:main(). */
static struct thread *initial_thread;

/* Lock used by allocate_tid(). */
static struct lock tid_lock;

/* Thread destruction requests */
static struct list destruction_req;

/* modify-mlfqs */
static struct list priority_queue_list;
static int load_avg; 	// fixed_point
static int ready_thread;
/* modify-mlfqs */


/* Statistics. */
static long long idle_ticks;    /* # of timer ticks spent idle. */
static long long kernel_ticks;  /* # of timer ticks in kernel threads. */
static long long user_ticks;    /* # of timer ticks in user programs. */

/* Scheduling. */
#define TIME_SLICE 4            /* # of timer ticks to give each thread. */
static unsigned thread_ticks;   /* # of timer ticks since last yield. */

/* If false (default), use round-robin scheduler.
   If true, use multi-level feedback queue scheduler.
   Controlled by kernel command-line option "-o mlfqs". */
bool thread_mlfqs;

static void kernel_thread (thread_func *, void *aux);

static void idle (void *aux UNUSED);
static struct thread *next_thread_to_run (void);
static void init_thread (struct thread *, const char *name, int priority);
static void do_schedule(int status);
static void schedule (void);
static tid_t allocate_tid (void);

/* Returns true if T appears to point to a valid thread. */
#define is_thread(t) ((t) != NULL && (t)->magic == THREAD_MAGIC)

/* Returns the running thread.
 * Read the CPU's stack pointer `rsp', and then round that
 * down to the start of a page.  Since `struct thread' is
 * always at the beginning of a page and the stack pointer is
 * somewhere in the middle, this locates the curent thread. */
#define running_thread() ((struct thread *) (pg_round_down (rrsp ())))


// Global descriptor table for the thread_start.
// Because the gdt will be setup after the thread_init, we should
// setup temporal gdt first.
static uint64_t gdt[3] = { 0, 0x00af9a000000ffff, 0x00cf92000000ffff };

static bool
is_interior (struct list_elem *elem) {
	return elem != NULL && elem->prev != NULL && elem->next != NULL;
}

/*modify-priority*/
bool priority_less_func (const struct list_elem *a,
                         const struct list_elem *b,
                         void *aux){
	const struct thread* t1 = list_entry(a, struct thread, elem);
	const struct thread* t2 = list_entry(b, struct thread, elem);

	return t1->priority > t2->priority;
}
/*modify-priority*/

/*modify-mlfqs*/
bool priority_less_func_mlfqs (const struct list_elem *a,
                         	   const struct list_elem *b,
                         	   void *aux){
	const struct thread* t1 = list_entry(a, struct thread, sema_elem);
	const struct thread* t2 = list_entry(b, struct thread, sema_elem);

	return t1->priority > t2->priority;
}
/*modify-mlfqs*/

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
void
thread_init (void) {

	ASSERT (intr_get_level () == INTR_OFF);

	/* Reload the temporal gdt for the kernel
	 * This gdt does not include the user context.
	 * The kernel will rebuild the gdt with user context, in gdt_init (). */
	struct desc_ptr gdt_ds = {
		.size = sizeof (gdt) - 1,
		.address = (uint64_t) gdt
	};
	lgdt (&gdt_ds);

	/* Init the globla thread context */
	lock_init (&tid_lock);
	list_init (&ready_list);
	list_init (&destruction_req);
	// [modify-alarmclock]
	list_init(&sleep_list);
	min_sleep_tick = INT64_MAX;
	// [modify-alarmclock]

	/* Set up a thread structure for the running thread. */
	initial_thread = running_thread ();
	/*modify-mlfqs*/
	p_q_l_init_done = false;
	initial_thread->nice = 0;
	initial_thread->recent_cpu = 0;
	// ready_thread++;
	/*modify-mlfqs*/
	init_thread (initial_thread, "main", PRI_DEFAULT);
	/*modify_mlfqs*/
	// thread_unblock(initial_thread);
	/*modify_mlfqs*/

	initial_thread->status = THREAD_RUNNING;
	initial_thread->tid = allocate_tid ();

	// [modify-alarmclock]
	initial_thread->tick_sleep = INT64_MAX;
	// [modify-alarmclock]

	/*modify-mlfqs*/
	load_avg = int_to_fixed_p(0);
	ready_thread = 1;
	/*modify-mlfqs*/
}

/* Starts preemptive thread scheduling by enabling interrupts.
   Also creates the idle thread. */
void
thread_start (void) {
	/* Create the idle thread. */
	if (thread_mlfqs) {
		list_init(&priority_queue_list);
		for (int i = PRI_MIN; i <= PRI_MAX; i++) {
			struct priority_queue* q = (struct priority_queue*) malloc(sizeof(struct priority_queue));
			memset(q, 0, sizeof(*q));
			list_init(&q->queue);
			q->priority = i;
			list_push_front(&priority_queue_list, &q->elem);
		}
	}
	
	struct semaphore idle_started;
	sema_init (&idle_started, 0);
	thread_create ("idle", PRI_MIN, idle, &idle_started);

	/* Start preemptive thread scheduling. */
	intr_enable ();

	/* Wait for the idle thread to initialize idle_thread. */
	sema_down (&idle_started);
	p_q_l_init_done = true;
}

void clip_priority(struct thread* t) {
	if (t->priority < PRI_MIN) t->priority = PRI_MIN;
	else if (t->priority > PRI_MAX) t->priority = PRI_MAX;
}

/* Called by the timer interrupt handler at each timer tick.
   Thus, this function runs in an external interrupt context. */
void
thread_tick (void) {


	struct thread *curr = thread_current ();

	/* Update statistics. */
	if (curr == idle_thread)
		idle_ticks++;
#ifdef USERPROG
	else if (t->pml4 != NULL)
		user_ticks++;
#endif
	else
		kernel_ticks++;

	/*modify-mlfqs*/
	curr->recent_cpu = fixed_p_add_int(curr->recent_cpu, 1);
	/*modify-mlfqs*/

	/* Enforce preemption. */
	if (++thread_ticks >= TIME_SLICE)
		intr_yield_on_return ();

	/*modify-mlfqs*/
	if (thread_mlfqs) {
		// enum intr_level old_level;
		// old_level = intr_disable ();
		int64_t curr_tick = timer_ticks();
		if (curr_tick % TIMER_FREQ == 0) { // every 1 seconds
			int x, y, z, alpha, beta;
			x = int_to_fixed_p(59);
			z = int_to_fixed_p(1);
			y = int_to_fixed_p(60);
			
			alpha = fixed_p_div_fixed_p(x, y);     // 59/60
			beta = fixed_p_div_fixed_p(z, y);      // 1/60

			// load avg update
			int r_t = 0;
			if (curr != idle_thread) r_t++;
			for (struct list_elem* e_ql = list_begin(&priority_queue_list); e_ql != list_end(&priority_queue_list); e_ql = list_next(e_ql)) {
				struct priority_queue* q = list_entry(e_ql, struct priority_queue, elem);
				for (struct list_elem* e_q = list_begin(&q->queue); e_q != list_end(&q->queue); e_q = list_next(e_q)) {
					if (list_entry(e_q, struct thread, elem) != idle_thread) r_t++;
				}
			}
			
			// load_avg = fixed_p_add_fixed_p(fixed_p_mul_fixed_p(alpha, load_avg), fixed_p_mul_int(beta, ready_thread));
			load_avg = fixed_p_add_fixed_p(fixed_p_mul_fixed_p(alpha, load_avg), fixed_p_mul_int(beta, r_t));
			barrier();

			// recent cpu update through priority_queue_list
			for (struct list_elem* e_ql = list_begin(&priority_queue_list); e_ql != list_end(&priority_queue_list); e_ql = list_next(e_ql)) {
				struct priority_queue* q = list_entry(e_ql, struct priority_queue, elem);
				for (struct list_elem* e_q = list_begin(&q->queue); e_q != list_end(&q->queue); e_q = list_next(e_q)) {
					struct thread* th = list_entry(e_q, struct thread, elem);
					th->recent_cpu = fixed_p_add_int(fixed_p_mul_fixed_p(fixed_p_div_fixed_p(fixed_p_mul_int(load_avg, 2), fixed_p_add_int(fixed_p_mul_int(load_avg, 2), 1)), th->recent_cpu), th->nice);
				}
			}
			// recent cpu update current thread
			curr->recent_cpu = fixed_p_add_int(fixed_p_mul_fixed_p(fixed_p_div_fixed_p(fixed_p_mul_int(load_avg, 2), fixed_p_add_int(fixed_p_mul_int(load_avg, 2), 1)), curr->recent_cpu), curr->nice);

			// recent cpu update through sleep list
			for (struct list_elem* e_s = list_begin(&sleep_list); e_s != list_end(&sleep_list); e_s = list_next(e_s)) {
				struct thread* t = list_entry(e_s, struct thread, elem);
				t->recent_cpu = fixed_p_add_int(fixed_p_mul_fixed_p(fixed_p_div_fixed_p(fixed_p_mul_int(load_avg, 2), fixed_p_add_int(fixed_p_mul_int(load_avg, 2), 1)), t->recent_cpu), t->nice);
			}
			// recent cpu update done
		}
		if (curr_tick % 4 == 0) {
			int p_max = int_to_fixed_p(PRI_MAX); // fixed point pri max

			// priority update through priority_queue_list
			for (struct list_elem* e_ql = list_begin(&priority_queue_list); e_ql != list_end(&priority_queue_list); e_ql = list_next(e_ql)) {
				struct priority_queue* q = list_entry(e_ql, struct priority_queue, elem);
				for (struct list_elem* e_q = list_begin(&q->queue); e_q != list_end(&q->queue); ) {
					struct thread* th = list_entry(e_q, struct thread, elem);
					int p; // fixed_point of priority value
					p = fixed_p_sub_fixed_p(p_max, fixed_p_add_fixed_p(fixed_p_div_int(th->recent_cpu, 4), int_to_fixed_p(th->nice * 2)));
					th->priority = fixed_p_to_int_down(p);

					clip_priority(th);

					if (th->priority != q->priority){
						struct list_elem* e_q_next = list_next(e_q);
						list_remove(e_q);
						struct list_elem* temp_e_ql = list_rbegin(&priority_queue_list);
						for (int i = PRI_MIN; i < th->priority; i++){
							temp_e_ql = list_prev(temp_e_ql);
						}
						struct priority_queue* temp_q = list_entry(temp_e_ql, struct priority_queue, elem);
						list_push_back(&temp_q->queue, e_q);
						e_q = e_q_next;
					}
					else {
						e_q = list_next(e_q);
					}
				}
			}

			// priority update current thread
			int curr_p; // fixed_point of current priority value
			curr_p = fixed_p_sub_fixed_p(p_max, fixed_p_add_fixed_p(fixed_p_div_int(curr->recent_cpu, 4), int_to_fixed_p(curr->nice * 2)));
			curr->priority = fixed_p_to_int_down(curr_p);

			clip_priority(curr);

			//priority update through sleep list
			for (struct list_elem* e_s = list_begin(&sleep_list); e_s != list_end(&sleep_list); e_s = list_next(e_s)) {
				struct thread* t = list_entry(e_s, struct thread, elem);
				int p_s;
				p_s = fixed_p_sub_fixed_p(p_max, fixed_p_add_fixed_p(fixed_p_div_int(t->recent_cpu, 4), int_to_fixed_p(t->nice * 2)));
				t->priority = fixed_p_to_int_down(p_s);

				clip_priority(t);
			}

			// keep idle min priority
			idle_thread->priority = PRI_MIN;
		}
		// intr_set_level (old_level);
	}
	/*modify-mlfqs*/
}

// [modify-alarmclock]
void thread_sleep(int64_t ticks) {
	ASSERT (intr_get_level () == INTR_ON);
	enum intr_level old_level;
	old_level = intr_disable ();
	ASSERT (thread_current() != idle_thread);

	struct thread *curr = thread_current ();

	int64_t curticks = timer_ticks();
	
	curr->tick_sleep = ticks + curticks;
	struct list_elem* e = &curr->elem;
	if (e != NULL && e->prev != NULL && e->next != NULL) {
		while(true){
			if (e != NULL && e->prev != NULL && e->next == NULL) {
				break;
			}
			else {
				e = list_next(e);
			}
		}
		if (e == list_tail(&ready_list)) list_remove(&curr->elem);
	}
	// list_push_back (&sleep_list, &curr->elem);

	if (min_sleep_tick > (ticks+curticks)) {
		min_sleep_tick = (ticks+curticks);
	}
	thread_block();
	intr_set_level (old_level);
}

void thread_wake(void){
	// enum intr_level old_level;
	// old_level = intr_disable ();
	if (timer_ticks() >= min_sleep_tick){
		struct list_elem* element;
		element = list_begin(&sleep_list);
		min_sleep_tick = INT64_MAX;
		int64_t curticks = timer_ticks();
		while (element!= list_tail(&sleep_list)){
			struct thread *t;
			t = list_entry(element, struct thread, elem);
			element = list_next(element);
			if (t->tick_sleep <= curticks) {
				t->tick_sleep = INT64_MAX;
				// list_remove(&t->elem);
				// t->elem.prev = NULL;
				// t->elem.next = NULL;
				thread_unblock(t);
			}
			else {
				if (min_sleep_tick > t->tick_sleep) {
					min_sleep_tick = t->tick_sleep;
				}
			}
		}
	}
	// intr_set_level (old_level);
}
// [modify-alarmclock]

/* Prints thread statistics. */
void
thread_print_stats (void) {
	printf ("Thread: %lld idle ticks, %lld kernel ticks, %lld user ticks\n",
			idle_ticks, kernel_ticks, user_ticks);
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
tid_t
thread_create (const char *name, int priority,
		thread_func *function, void *aux) {
	struct thread *t;
	tid_t tid;

	ASSERT (function != NULL);

	/* Allocate thread. */
	t = palloc_get_page (PAL_ZERO);
	if (t == NULL)
		return TID_ERROR;

	/* Initialize thread. */
	init_thread (t, name, priority);
	tid = t->tid = allocate_tid ();
	
	/*modify-mlfqs*/
	t->nice = thread_current()->nice;
	t->recent_cpu = thread_current()->recent_cpu;
	/*modify-mlfqs*/

	/* Call the kernel_thread if it scheduled.
	 * Note) rdi is 1st argument, and rsi is 2nd argument. */
	t->tf.rip = (uintptr_t) kernel_thread;
	t->tf.R.rdi = (uint64_t) function;
	t->tf.R.rsi = (uint64_t) aux;
	t->tf.ds = SEL_KDSEG;
	t->tf.es = SEL_KDSEG;
	t->tf.ss = SEL_KDSEG;
	t->tf.cs = SEL_KCSEG;
	t->tf.eflags = FLAG_IF;

	/* Add to run queue. */
	thread_unblock (t);
	
	/* modify-priority */
	yield_if_lower();
	/* modify-priority */

	return tid;
}

/* Puts the current thread to sleep.  It will not be scheduled
   again until awoken by thread_unblock().

   This function must be called with interrupts turned off.  It
   is usually a better idea to use one of the synchronization
   primitives in synch.h. */
void
thread_block (void) {
	ASSERT (!intr_context ());
	ASSERT (intr_get_level () == INTR_OFF);
	ASSERT (ready_thread >= 0);
	
	struct thread* curr = thread_current();
	/*modify-mlfqs*/
	if (thread_mlfqs) {
		//TODO
		if (curr->elem.prev != NULL && curr->elem.next != NULL) {
			printf("why running thread is inside some list?");
		}
		if (strcmp(thread_current()->name, "idle")) {
			ready_thread--;
		}
	}
	else {
		/*modify-mlfqs*/
		struct list_elem* e = &curr->elem;
		if (e != NULL && e->prev != NULL && e->next != NULL) {
			while(true){
				if (e != NULL && e->prev != NULL && e->next == NULL) {
					break;
				}
				else {
					e = list_next(e);
				}
			}
			if (e == list_tail(&ready_list) || e == list_tail(&sleep_list)) {
				list_remove(&curr->elem); // remove from ready list & sleep_list only
				curr->elem.next = NULL;
				curr->elem.prev = NULL;
			}
		}
		/*modify-mlfqs*/
	}
	list_push_back(&sleep_list, &curr->elem);
	/*modify-mlfqs*/
	curr->status = THREAD_BLOCKED;
	schedule ();
}

/* Transitions a blocked thread T to the ready-to-run state.
   This is an error if T is not blocked.  (Use thread_yield() to
   make the running thread ready.)

   This function does not preempt the running thread.  This can
   be important: if the caller had disabled interrupts itself,
   it may expect that it can atomically unblock a thread and
   update other data. */
void
thread_unblock (struct thread *t) {
	enum intr_level old_level;

	ASSERT (is_thread (t));
	ASSERT (ready_thread >= 0);

	old_level = intr_disable ();
	ASSERT (t->status == THREAD_BLOCKED);
	/*modify-priority*/
	if (is_interior(&t->elem)) {
		list_remove(&t->elem);
		t->elem.prev = NULL;
		t->elem.next = NULL;
	}
	// list_push_back (&ready_list, &t->elem);
	if (!thread_mlfqs) {
		list_insert_ordered(&ready_list, &t->elem, priority_less_func, NULL);
	}
	/*modify-priority*/
	/*modify-mlfqs*/
	else {
		//TODO

		// push back to priority queue which has same priority
		for (struct list_elem* e_ql = list_begin(&priority_queue_list); e_ql != list_end(&priority_queue_list); e_ql = list_next(e_ql)) {
			struct priority_queue* q = list_entry(e_ql, struct priority_queue, elem);
			if (q->priority == t->priority) {
				list_push_back(&q->queue, &t->elem);
				break;
			}
		}

		// ready thread counting
		if (strcmp(t->name, "idle")) ready_thread++;
	}
	/*modify-mlfqs*/
	t->status = THREAD_READY;
	intr_set_level (old_level);
}

/* Returns the name of the running thread. */
const char *
thread_name (void) {
	return thread_current ()->name;
}

/* Returns the running thread.
   This is running_thread() plus a couple of sanity checks.
   See the big comment at the top of thread.h for details. */
struct thread *
thread_current (void) {
	struct thread *t = running_thread ();

	/* Make sure T is really a thread.
	   If either of these assertions fire, then your thread may
	   have overflowed its stack.  Each thread has less than 4 kB
	   of stack, so a few big automatic arrays or moderate
	   recursion can cause stack overflow. */
	ASSERT (is_thread (t));
	ASSERT (t->status == THREAD_RUNNING);

	return t;
}

/* Returns the running thread's tid. */
tid_t
thread_tid (void) {
	return thread_current ()->tid;
}

/* Deschedules the current thread and destroys it.  Never
   returns to the caller. */
void
thread_exit (void) {
	ASSERT (!intr_context ());

#ifdef USERPROG
	process_exit ();
#endif

	/* Just set our status to dying and schedule another process.
	   We will be destroyed during the call to schedule_tail(). */
	intr_disable ();
	/*modify-mlfqs*/
	if (thread_mlfqs) {
		if (strcmp(thread_current()->name, "idle")) ready_thread--;
	}	
	
	/*modify-mlfqs*/
	if (!strcmp(thread_current()->name, "main")) {
		for (struct list_elem* e = list_begin(&priority_queue_list); e != list_end(&priority_queue_list); ) {
			struct list_elem* next_e = list_next(e);
			struct priority_queue* q = list_entry(e, struct priority_queue, elem);
			free(q);
			e = next_e;
		}
	}
	/*modify-mlfqs*/

	/*modify-mlfqs*/
	do_schedule (THREAD_DYING);
	NOT_REACHED ();
}

/* Yields the CPU.  The current thread is not put to sleep and
   may be scheduled again immediately at the scheduler's whim. */
void
thread_yield (void) {
	struct thread *curr = thread_current ();
	ASSERT (!intr_context ());
	enum intr_level old_level;
	old_level = intr_disable ();

	// if (curr != idle_thread) {
		/*modify-priority*/
	if (!thread_mlfqs) {
		if (list_empty(&ready_list)) {
			intr_set_level (old_level);
			return;
		}	
		if (!list_empty(&ready_list)){
			struct list_elem* e = &curr->elem;
			if (e != NULL && e->prev != NULL && e->next != NULL) {
				while (true) {
					if (e != NULL && e->prev != NULL && e->next == NULL) {
						break;
					}
					else {
						e = list_next(e);
					}
				}
				if (e == list_tail(&ready_list)) list_remove(&curr->elem);
			}
		}
		list_insert_ordered(&ready_list, &curr->elem, priority_less_func, NULL);
	}
	/*modify-priority*/
	/*modify-mlfqs*/
	else {
		//TODO
		// push back to priority queue which has same priority
		if (curr->elem.next != NULL && curr->elem.prev != NULL) printf("why running thread is interior some list?\n");
		for (struct list_elem* e_ql = list_begin(&priority_queue_list); e_ql != list_end(&priority_queue_list); e_ql = list_next(e_ql)) {
			struct priority_queue* q = list_entry(e_ql, struct priority_queue, elem);
			if (q->priority == curr->priority) {
				list_push_back(&q->queue, &curr->elem);
				break;
			}
		}
	}
		/*modify-mlfqs*/
	// }
	do_schedule (THREAD_READY);
	intr_set_level (old_level);
}

/* modify-priority */
void yield_if_lower (void){
	// enum intr_level old_level;
	// old_level = intr_disable ();
	int curr_priority = thread_current()->priority;
	if (!thread_mlfqs){
		if (list_empty(&ready_list)) {
			// intr_set_level (old_level);
			return;
		}
		int highest_priority = list_entry(list_begin(&ready_list), struct thread, elem)->priority;
		if (curr_priority < highest_priority){
			thread_yield();
		}
	}
	/*modify-mlfqs*/
	else {
		//TODO
		int highest_priority = -1;
		for (struct list_elem* e_ql = list_begin(&priority_queue_list); e_ql != list_end(&priority_queue_list); e_ql = list_next(e_ql)) {
			struct priority_queue* q = list_entry(e_ql, struct priority_queue, elem);
			if (!list_empty(&q->queue)) {
				highest_priority = q->priority;
				break;
			}
		}
		if (highest_priority < 0) printf("do not reach here: why highest priority didn't set?");
		if (curr_priority < highest_priority){
			thread_yield();
		}
	}
	// intr_set_level (old_level);
	/*modify-mlfqs*/
}
/* modify-priority */

/* Sets the current thread's priority to NEW_PRIORITY. */
void
thread_set_priority (int new_priority) {
	struct thread* curr = thread_current();
	curr->origin_priority = new_priority;
	struct list* hll = &curr->having_lock_list;
	int max_priority = -1;
	for (struct list_elem* e = list_begin(hll); e != list_end(hll); e = list_next(e)) {
		if (list_empty(&list_entry(e, struct lock, elem)->semaphore.waiters)) continue;
		struct thread* t = list_entry(list_front(&list_entry(e, struct lock, elem)->semaphore.waiters), struct thread, sema_elem);
		if (t->priority > max_priority) max_priority = t->priority;
	}
	if (new_priority > max_priority){
		curr->priority = new_priority;
	}
	yield_if_lower();
}

/* Returns the current thread's priority. */
int
thread_get_priority (void) {
	return thread_current ()->priority;
}

/* Sets the current thread's nice value to NICE. */
void
thread_set_nice (int nice) {
	/* TODO: Your implementation goes here */
	struct thread* curr = thread_current();
	curr->nice = nice;
	int curr_p; // fixed_point of current priority value
	int p_max = int_to_fixed_p(PRI_MAX);
	curr_p = fixed_p_sub_fixed_p(p_max, fixed_p_add_fixed_p(fixed_p_div_int(curr->recent_cpu, 4), int_to_fixed_p(curr->nice * 2)));
	curr->priority = fixed_p_to_int_down(curr_p);
	clip_priority(curr);

	yield_if_lower();
}

/* Returns the current thread's nice value. */
int
thread_get_nice (void) {
	/* TODO: Your implementation goes here */
	return thread_current()->nice;
}

/* Returns 100 times the system load average. */
int
thread_get_load_avg (void) {
	/* TODO: Your implementation goes here */
	return fixed_p_to_int_nearest(fixed_p_mul_int(load_avg, 100));
}

/* Returns 100 times the current thread's recent_cpu value. */
int
thread_get_recent_cpu (void) {
	/* TODO: Your implementation goes here */
	return fixed_p_to_int_nearest(fixed_p_mul_int(thread_current()->recent_cpu, 100));
}

/* Idle thread.  Executes when no other thread is ready to run.

   The idle thread is initially put on the ready list by
   thread_start().  It will be scheduled once initially, at which
   point it initializes idle_thread, "up"s the semaphore passed
   to it to enable thread_start() to continue, and immediately
   blocks.  After that, the idle thread never appears in the
   ready list.  It is returned by next_thread_to_run() as a
   special case when the ready list is empty. */
static void
idle (void *idle_started_ UNUSED) {
	struct semaphore *idle_started = idle_started_;

	idle_thread = thread_current ();
	sema_up (idle_started);

	for (;;) {
		/* Let someone else run. */
		intr_disable ();
		thread_block ();

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
		asm volatile ("sti; hlt" : : : "memory");
	}
}

/* Function used as the basis for a kernel thread. */
static void
kernel_thread (thread_func *function, void *aux) {
	ASSERT (function != NULL);

	intr_enable ();       /* The scheduler runs with interrupts off. */
	function (aux);       /* Execute the thread function. */
	thread_exit ();       /* If function() returns, kill the thread. */
}


/* Does basic initialization of T as a blocked thread named
   NAME. */
static void
init_thread (struct thread *t, const char *name, int priority) {
	ASSERT (t != NULL);
	ASSERT (PRI_MIN <= priority && priority <= PRI_MAX);
	ASSERT (name != NULL);

	memset (t, 0, sizeof *t);
	t->status = THREAD_BLOCKED;
	strlcpy (t->name, name, sizeof t->name);
	t->tf.rsp = (uint64_t) t + PGSIZE - sizeof (void *);
	t->priority = priority;
	t->magic = THREAD_MAGIC;
	/*modify-priority*/
	list_init(&t->having_lock_list);
	t->waiting_lock = NULL;
	t->origin_priority = priority;
	/*modify-priority*/
}

/* Chooses and returns the next thread to be scheduled.  Should
   return a thread from the run queue, unless the run queue is
   empty.  (If the running thread can continue running, then it
   will be in the run queue.)  If the run queue is empty, return
   idle_thread. */
static struct thread *
next_thread_to_run (void) {
	/*modify-priority*/
	if (!thread_mlfqs) {
		if (list_empty (&ready_list)) {
			if (is_interior(&idle_thread->elem)) {
				list_remove(&idle_thread->elem);
				idle_thread->elem.next = NULL;
				idle_thread->elem.prev = NULL;
			}
			return idle_thread;
		}
		struct list_elem* e_;
		for (struct list_elem* e = list_begin(&ready_list); e != list_end(&ready_list);
			 e = list_next(e)) {
			// printf("%d", list_entry(e, struct thread, elem)->status);
			if (list_entry(e, struct thread, elem)->status == THREAD_READY){
				e_ = e;
				list_remove(e);
				e->next = NULL;
				e->prev = NULL;
				break;
			}
		}
		struct thread * t = list_entry (e_, struct thread, elem);

		// TODO: check it needed or not
		// list_remove(e);

		return t;
	}
	/*modify-priority*/
	/*modify-mlfqs*/
	else {
		//TODO
		struct thread* t;
		t = idle_thread;
		for (struct list_elem* e_ql = list_begin(&priority_queue_list); e_ql != list_end(&priority_queue_list); e_ql = list_next(e_ql)) {
			struct priority_queue* q = list_entry(e_ql, struct priority_queue, elem);
			if (!list_empty(&q->queue)) {
				t = list_entry(list_pop_front(&q->queue), struct thread, elem);
				t->elem.next = NULL;
				t->elem.prev = NULL;
				break;
			}
		}
		if (t == idle_thread) {
			if (is_interior(&idle_thread->elem)) {
				list_remove(&idle_thread->elem);
			}
			idle_thread->elem.next = NULL;
			idle_thread->elem.prev = NULL;
		}
		return t;
	}
	/*modify-mlfqs*/
}

/* Use iretq to launch the thread */
void
do_iret (struct intr_frame *tf) {
	__asm __volatile(
			"movq %0, %%rsp\n"
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
			: : "g" ((uint64_t) tf) : "memory");
}

/* Switching the thread by activating the new thread's page
   tables, and, if the previous thread is dying, destroying it.

   At this function's invocation, we just switched from thread
   PREV, the new thread is already running, and interrupts are
   still disabled.

   It's not safe to call printf() until the thread switch is
   complete.  In practice that means that printf()s should be
   added at the end of the function. */
static void
thread_launch (struct thread *th) {
	uint64_t tf_cur = (uint64_t) &running_thread ()->tf;
	uint64_t tf = (uint64_t) &th->tf;
	ASSERT (intr_get_level () == INTR_OFF);

	/* The main switching logic.
	 * We first restore the whole execution context into the intr_frame
	 * and then switching to the next thread by calling do_iret.
	 * Note that, we SHOULD NOT use any stack from here
	 * until switching is done. */
	__asm __volatile (
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
			"pop %%rbx\n"              // Saved rcx
			"movq %%rbx, 96(%%rax)\n"
			"pop %%rbx\n"              // Saved rbx
			"movq %%rbx, 104(%%rax)\n"
			"pop %%rbx\n"              // Saved rax
			"movq %%rbx, 112(%%rax)\n"
			"addq $120, %%rax\n"
			"movw %%es, (%%rax)\n"
			"movw %%ds, 8(%%rax)\n"
			"addq $32, %%rax\n"
			"call __next\n"         // read the current rip.
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
			: : "g"(tf_cur), "g" (tf) : "memory"
			);
}

/* Schedules a new process. At entry, interrupts must be off.
 * This function modify current thread's status to status and then
 * finds another thread to run and switches to it.
 * It's not safe to call printf() in the schedule(). */
static void
do_schedule(int status) {
	ASSERT (intr_get_level () == INTR_OFF);
	ASSERT (thread_current()->status == THREAD_RUNNING);
	while (!list_empty (&destruction_req)) {
		struct thread *victim =
			list_entry (list_pop_front (&destruction_req), struct thread, elem);
		palloc_free_page(victim);
	}
	thread_current ()->status = status;
	schedule ();
}

static void
schedule (void) {
	struct thread *curr = running_thread ();
	struct thread *next = next_thread_to_run ();

	ASSERT (intr_get_level () == INTR_OFF);
	ASSERT (curr->status != THREAD_RUNNING);
	ASSERT (is_thread (next));
	/* Mark us as running. */
	next->status = THREAD_RUNNING;

	/* Start new time slice. */
	thread_ticks = 0;

#ifdef USERPROG
	/* Activate the new address space. */
	process_activate (next);
#endif

	if (curr != next) {
		/* If the thread we switched from is dying, destroy its struct
		   thread. This must happen late so that thread_exit() doesn't
		   pull out the rug under itself.
		   We just queuing the page free reqeust here because the page is
		   currently used bye the stack.
		   The real destruction logic will be called at the beginning of the
		   schedule(). */
		if (curr && curr->status == THREAD_DYING && curr != initial_thread) {
			ASSERT (curr != next);
			list_push_back (&destruction_req, &curr->elem);
		}

		/* Before switching the thread, we first save the information
		 * of current running. */
		thread_launch (next);
	}
}

/* Returns a tid to use for a new thread. */
static tid_t
allocate_tid (void) {
	static tid_t next_tid = 1;
	tid_t tid;

	lock_acquire (&tid_lock);
	tid = next_tid++;
	lock_release (&tid_lock);

	return tid;
}
