
#include <limits.h>
#include <assert.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <math.h>

#include "host.h"
#include "misc.h"
#include "machine.h"
#include "regs.h"
#include "memory.h"
#include "loader.h"
#include "syscall.h"
#include "dlite.h"
#include "options.h"
#include "stats.h"
#include "sim.h"
#include "decode.def"

#include "instr.h"

/* PARAMETERS OF THE TOMASULO'S ALGORITHM */

#define INSTR_QUEUE_SIZE         10

#define RESERV_INT_SIZE    4
#define RESERV_FP_SIZE     2
#define FU_INT_SIZE        2
#define FU_FP_SIZE         1

#define FU_INT_LATENCY     4
#define FU_FP_LATENCY      9

/* IDENTIFYING INSTRUCTIONS */

//unconditional branch, jump or call
#define IS_UNCOND_CTRL(op) (MD_OP_FLAGS(op) & F_CALL || \
                         MD_OP_FLAGS(op) & F_UNCOND)

//conditional branch instruction
#define IS_COND_CTRL(op) (MD_OP_FLAGS(op) & F_COND)

//floating-point computation
#define IS_FCOMP(op) (MD_OP_FLAGS(op) & F_FCOMP)

//integer computation
#define IS_ICOMP(op) (MD_OP_FLAGS(op) & F_ICOMP)

//load instruction
#define IS_LOAD(op)  (MD_OP_FLAGS(op) & F_LOAD)

//store instruction
#define IS_STORE(op) (MD_OP_FLAGS(op) & F_STORE)

//trap instruction
#define IS_TRAP(op) (MD_OP_FLAGS(op) & F_TRAP) 

#define USES_INT_FU(op) (IS_ICOMP(op) || IS_LOAD(op) || IS_STORE(op))
#define USES_FP_FU(op) (IS_FCOMP(op))

#define WRITES_CDB(op) (IS_ICOMP(op) || IS_LOAD(op) || IS_FCOMP(op))

#define IS_BRANCH(op) (IS_COND_CTRL(op) || IS_UNCOND_CTRL(op))

/* FOR DEBUGGING */

//prints info about an instruction
#define PRINT_INST(out,instr,str,cycle)	\
  myfprintf(out, "%d: %s", cycle, str);		\
  md_print_insn(instr->inst, instr->pc, out); \
  myfprintf(stdout, "(%d)\n",instr->index);

#define PRINT_REG(out,reg,str,instr) \
  myfprintf(out, "reg#%d %s ", reg, str);	\
  md_print_insn(instr->inst, instr->pc, out); \
  myfprintf(stdout, "(%d)\n",instr->index);

/* VARIABLES */

//instruction queue for tomasulo
static instruction_t* instr_queue[INSTR_QUEUE_SIZE];
//number of instructions in the instruction queue
static int instr_queue_size = 0;

//reservation stations (each reservation station entry contains a pointer to an instruction)
static instruction_t* reservINT[RESERV_INT_SIZE];
static instruction_t* reservFP[RESERV_FP_SIZE];

//functional units
static instruction_t* fuINT[FU_INT_SIZE];
static instruction_t* fuFP[FU_FP_SIZE];

//common data bus
static instruction_t* commonDataBus = NULL;

//The map table keeps track of which instruction produces the value for each register
static instruction_t* map_table[MD_TOTAL_REGS];

//the index of the last instruction fetched
static int fetch_index = 0;

/* FUNCTIONAL UNITS */


/* RESERVATION STATIONS */

int push_to_IFQ(instruction_t *instr) {
    int i = 0;
    for(; i < INSTR_QUEUE_SIZE; i++) {
        if(instr_queue[i] == NULL) {
            instr_queue[i] = instr;
            return 1;
        }
    }
    
    return 0;
}


instruction_t *pop_from_IFQ() {
    instruction_t *instr = instr_queue[0];
    int i = 1;
    
    for(; i < INSTR_QUEUE_SIZE; i++) {
        instr_queue[i-1] = instr_queue[i];
        instr_queue[i] = NULL;
    }
    
    return instr
}

int push_to_resource(instruction_t** queue, int size, instruction_t* instr) {
    int i = 0;
    for(; i < size; i++) {
        if(queue[i] == NULL) {
            queue[i] = instr;
            return i;
        }
    }
    
    return -1;
}

void update_map_table(instruction_t *instr) {
    int i = 0;
    for(; i < 2; i++) {
        r_out = instr->r_out[i]
        if(r_out != NULL) {
            //checking for valid output reg
            map_table[r_out] = instr;
        }
    }
}

void clear_map_table(instruction_t *instr) {
    int i = 0;
    for(; i < 2; i++) {
        r_out = instr->r_out[i]
        if(map_table[r_out] == instr) {
            //if this intruction was the last to rename r_out
            map_table[r_out] = NULL;
        }
    }
}

/* 
 * Description: 
 * 	Checks if simulation is done by finishing the very last instruction
 *      Remember that simulation is done only if the entire pipeline is empty
 * Inputs:
 * 	sim_insn: the total number of instructions simulated
 * Returns:
 * 	True: if simulation is finished
 */
static bool is_simulation_done(counter_t sim_insn) {

  /* ECE552: YOUR CODE GOES HERE */

  return true; //ECE552: you can change this as needed; we've added this so the code provided to you compiles
}

/* 
 * Description: 
 * 	Retires the instruction from writing to the Common Data Bus
 * Inputs:
 * 	current_cycle: the cycle we are at
 * Returns:
 * 	None
 */
void CDB_To_retire(int current_cycle) {

  /* ECE552: YOUR CODE GOES HERE */

}


/* 
 * Description: 
 * 	Moves an instruction from the execution stage to common data bus (if possible)
 * Inputs:
 * 	current_cycle: the cycle we are at
 * Returns:
 * 	None
 */
void execute_To_CDB(int current_cycle) {

  /* ECE552: YOUR CODE GOES HERE */

}

/* 
 * Description: 
 * 	Moves instruction(s) from the issue to the execute stage (if possible). We prioritize old instructions
 *      (in program order) over new ones, if they both contend for the same functional unit.
 *      All RAW dependences need to have been resolved with stalls before an instruction enters execute.
 * Inputs:
 * 	current_cycle: the cycle we are at
 * Returns:
 * 	None
 */
void issue_To_execute(int current_cycle) {

  /* ECE552: YOUR CODE GOES HERE */
}

/* 
 * Description: 
 * 	Moves instruction(s) from the dispatch stage to the issue stage
 * Inputs:
 * 	current_cycle: the cycle we are at
 * Returns:
 * 	None
 */
void dispatch_To_issue(int current_cycle) {

  /* ECE552: YOUR CODE GOES HERE */
    
}

/* 
 * Description: 
 * 	Grabs an instruction from the instruction trace (if possible)
 * Inputs:
 *      trace: instruction trace with all the instructions executed
 * Returns:
 * 	None
 */
void fetch(instruction_trace_t* trace) {

  /* ECE552: YOUR CODE GOES HERE */
    instruction_t* instr = get_instr(trace, fetch_index);
    
    while(IS_TRAP(instr->op)) instr = get_instr(trace, ++fetch_index);
    
    int pushed = push_to_IFQ(instr);
    if(pushed) {
        fetch_index++;
    }
}

/* 
 * Description: 
 * 	Calls fetch and dispatches an instruction at the same cycle (if possible)
 * Inputs:
 *      trace: instruction trace with all the instructions executed
 * 	current_cycle: the cycle we are at
 * Returns:
 * 	None
 */
void fetch_To_dispatch(instruction_trace_t* trace, int current_cycle) {

  fetch(trace);
  
  /* ECE552: YOUR CODE GOES HERE */
    if(IS_BRANCH(instr_queue[0]->op)) {
        pop_from_IFQ();
        return;
    }
    
    instruction_t *next_instr = instr_queue[0];
    
    if(USES_INT_FU(next_instr->op)) {
        int pushed_to_RS = push_to_resource(reservINT, RESERV_INT_SIZE, next_instr);
        if(pushed_to_RS != -1) {
            next_instr->pop_from_IFQ();
            
            //update mapTable and dependencies in RS
            update_map_table(next_instr);
            int i = 0;
            for(; i < 3; i++) {
                r_in = next_instr->r_in[i];
                if(map_table[r_in] != NULL) {
                    next_instr->Q[i] = map_table[r_in];
                }
            }
            
            next_instr->tom_dispatch_cycle = current_cycle;
            return;
        }
    }
    
    if(USES_FP_FU(next_instr->op)) {
        int pushed_to_RS = push_to_resource(reservFP, RESERV_FP_SIZE, next_instr);
        if(pushed_to_RS != -1) {
            next_instr->pop_from_IFQ();
            
            //update mapTable and dependencies in RS
            update_map_table(next_instr);
            int i = 0;
            for(; i < 3; i++) {
                r_in = next_instr->r_in[i];
                if(map_table[r_in] != NULL) {
                    next_instr->Q[i] = map_table[r_in];
                }
            }
            
            next_instr->tom_dispatch_cycle = current_cycle;
            return;
        }
    }
    
    
    
}

/* 
 * Description: 
 * 	Performs a cycle-by-cycle simulation of the 4-stage pipeline
 * Inputs:
 *      trace: instruction trace with all the instructions executed
 * Returns:
 * 	The total number of cycles it takes to execute the instructions.
 * Extra Notes:
 * 	sim_num_insn: the number of instructions in the trace
 */
counter_t runTomasulo(instruction_trace_t* trace)
{
  //initialize instruction queue
  int i;
  for (i = 0; i < INSTR_QUEUE_SIZE; i++) {
    instr_queue[i] = NULL;
  }

  //initialize reservation stations
  for (i = 0; i < RESERV_INT_SIZE; i++) {
      reservINT[i] = NULL;
  }

  for(i = 0; i < RESERV_FP_SIZE; i++) {
      reservFP[i] = NULL;
  }

  //initialize functional units
  for (i = 0; i < FU_INT_SIZE; i++) {
    fuINT[i] = NULL;
  }

  for (i = 0; i < FU_FP_SIZE; i++) {
    fuFP[i] = NULL;
  }

  //initialize map_table to no producers
  int reg;
  for (reg = 0; reg < MD_TOTAL_REGS; reg++) {
    map_table[reg] = NULL;
  }
  
  int cycle = 1;
  while (true) {

     /* ECE552: YOUR CODE GOES HERE */

     cycle++;

     if (is_simulation_done(sim_num_insn))
        break;
  }
  
  return cycle;
}
