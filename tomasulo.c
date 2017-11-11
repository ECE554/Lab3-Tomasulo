
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

#define NUM_INPUT_REGS 3
#define NUM_OUTPUT_REGS 2

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

/* Utility Functions */

//Set references to producers of input values
void set_RAW_hazards(instruction_t* dispatched_instr) {
    for (int i = 0; i < NUM_INPUT_REGS; i++) {
        int reg = dispatched_instr->r_in[i];
        if (reg > 0) {
            dispatched_instr->Q[i] = map_table[reg];
        }
    }
}

//Set this instr as the latest producer of its output regs
void update_map_table(instruction_t* dispatched_instr) {
    for (int i = 0; i < NUM_OUTPUT_REGS; i++) {
        int reg = dispatched_instr->r_out[i];
        if (reg > 0) {
            map_table[reg] = dispatched_instr;
        }
    }
}

//Check to see if all RAW hazards have been resolved
bool instruction_ready(instruction_t* instr) {
    for (int i = 0; i < NUM_INPUT_REGS; i++) {
        if (instr->Q[i] == NULL) continue;
        if (instr->Q[i]->tom_cdb_cycle == 0) {
            return false;
        }
    }
    return true;
}

//Check if available spot in list
int available_list_index(instruction_t** list, int size) {
    for (int i = 0; i < size; i++) {
        if (list[i] == NULL) return i;
    }
    return -1;
}

/* END Utility Functions */

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
    
    if (fetch_index >= sim_num_insn) return; //No more instructions to fetch

    //Find free spot:
    int free_index = available_list_index(instr_queue, INSTR_QUEUE_SIZE);
    if (free_index == -1) return; //IFQ FULL

    //Get next non-trap instruction
    instruction_t* instr = get_instr(trace, fetch_index);
    while(IS_TRAP(instr->op)){
        fetch_index++;
        instr = get_instr(trace, fetch_index);
    };

    //Insert next instr into queue
    instr_queue[free_index] = instr;
    fetch_index++;
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

    /* ECE552: YOUR CODE GOES HERE */
    fetch(trace);
    
    instruction_t* next_instr = instr_queue[0]; //Get front of queue
    
    if (next_instr == NULL) return; //QUEUE EMPTY

    if (IS_BRANCH(next_instr->op)) {
        
        next_instr->tom_dispatch_cycle = current_cycle;
        //Nothing else to do, branches are ignored
    
    } 

    else if (USES_INT_FU(next_instr->op)) {

        //Look for free spot in reserv
        int free_index = available_list_index(reservINT, RESERV_INT_SIZE);
        if (free_index == -1) return; //Reserv full, need to stall

        //Insert in reserv and update map table
        reservINT[free_index] = next_instr;

        next_instr->tom_dispatch_cycle = current_cycle;

        set_RAW_hazards(next_instr);
        update_map_table(next_instr);

    } 

    else if (USES_FP_FU(next_instr->op)) {
        
        //Look for free spot in reserv
        int free_index = available_list_index(reservFP, RESERV_FP_SIZE);
        if (free_index == -1) return; //Reserv full, need to stall

        //Insert in reserv and update map table
        reservFP[free_index] = next_instr;

        next_instr->tom_dispatch_cycle = current_cycle;
        
        set_RAW_hazards(next_instr);
        update_map_table(next_instr);

    }

    //MOVE INSTRUCTION QUEUE FORWARD
    for (int i = 1; i < INSTR_QUEUE_SIZE; i++) {
        instr_queue[i-1] = instr_queue[i];
    }
    instr_queue[INSTR_QUEUE_SIZE - 1] = NULL;

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

    //Check reserv for last dispatched instruction
    for (int i = 0; i < RESERV_INT_SIZE; i++) {
        if (reservINT[i] == NULL) continue;
        if (reservINT[i]->tom_issue_cycle == 0 && reservINT[i]->tom_dispatch_cycle < current_cycle) {
            reservINT[i]->tom_issue_cycle = current_cycle;
            break; //Only 1 instr issued / cycle
        }
    }

    for (int i = 0; i < RESERV_FP_SIZE; i++) {
        if (reservFP[i] == NULL) continue;
        if (reservFP[i]->tom_issue_cycle == 0 && reservFP[i]->tom_dispatch_cycle < current_cycle) {
            reservFP[i]->tom_issue_cycle = current_cycle;
            break; //Only 1 instr issued / cycle
        }
    }

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

    //INT STATION->FU
    int free_index = available_list_index(fuINT, FU_INT_SIZE);
    while (free_index != -1) {

        instruction_t* oldest_ready_instr = NULL;
        for (int i = 0; i < RESERV_INT_SIZE; i++) {
            if (reservINT[i] == NULL) continue;

            if (instruction_ready(reservINT[i])) {

                if (oldest_ready_instr == NULL) {
                    oldest_ready_instr = reservINT[i];
                }
                else if (oldest_ready_instr->index > reservINT[i]->index) {
                    oldest_ready_instr = reservINT[i];
                }
            }
        }
        
        if (oldest_ready_instr == NULL) break; //No instructions are ready, FU will remain vacant

        fuINT[free_index] = oldest_ready_instr;
        oldest_ready_instr->tom_execute_cycle = current_cycle;

        free_index = available_list_index(fuINT, FU_INT_SIZE);
    }

    //FP STATION->FU
    free_index = available_list_index(fuFP, FU_FP_SIZE);
    while (free_index != -1) {

        instruction_t* oldest_ready_instr = NULL;
        for (int i = 0; i < RESERV_FP_SIZE; i++) {
            if (reservFP[i] == NULL) continue;

            if (instruction_ready(reservFP[i])) {

                if (oldest_ready_instr == NULL) {
                    oldest_ready_instr = reservFP[i];
                }
                else if (oldest_ready_instr->index > reservFP[i]->index) {
                    oldest_ready_instr = reservFP[i];
                }
            }
        }
        
        if (oldest_ready_instr == NULL) break; //No instructions are ready, FU will remain vacant

        fuFP[free_index] = oldest_ready_instr;
        oldest_ready_instr->tom_execute_cycle = current_cycle;

        free_index = available_list_index(fuFP, FU_FP_SIZE);
    }
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
    bool oldest_is_int = false;
    int oldest_fu_index = -1;
    instruction_t* oldest_completed_instr = NULL;

    for (int i = 0; i < FU_INT_SIZE; i++) {
        if (fuINT[i] == NULL) continue;

        if (current_cycle - fuINT[i]->tom_execute_cycle >= FU_INT_LATENCY) {
            if (IS_STORE(fuINT[i]->op)){
                for (int j = 0; j < RESERV_INT_SIZE; j++) {
                    if (reservINT[j] == NULL) continue;
                    if (reservINT[j]->index == fuINT[i]->index) {
                        reservINT[j] = NULL;
                        break;
                    }
                }

                fuINT[i] = NULL;
                continue;
            }

            if (oldest_completed_instr == NULL || oldest_completed_instr->index > fuINT[i]->index) {
                oldest_is_int = true;
                oldest_fu_index = i;
                oldest_completed_instr = fuINT[i];
            }
        }
    }

    for (int i = 0; i < FU_FP_SIZE; i++) {
        if (fuFP[i] == NULL) continue;

        if (current_cycle - fuFP[i]->tom_execute_cycle >= FU_FP_LATENCY) {
            if (oldest_completed_instr == NULL || oldest_completed_instr->index > fuFP[i]->index) {
                oldest_is_int = false;
                oldest_fu_index = i;
                oldest_completed_instr = fuFP[i];
            }
        }
    }

    if (oldest_completed_instr == NULL) return; //No instructions ready to coimplete
    
    commonDataBus = oldest_completed_instr;
    commonDataBus->tom_cdb_cycle = current_cycle;

    //Remove from FU and Reserv
    if (oldest_is_int) {
        fuINT[oldest_fu_index] = NULL;

        for (int i = 0; i < RESERV_INT_SIZE; i++) {
            if (reservINT[i] == NULL) continue;
            if (reservINT[i]->index == oldest_completed_instr->index) {
                reservINT[i] = NULL;
                break;
            }
        }
    }
    else {
        fuFP[oldest_fu_index] = NULL;

        for (int i = 0; i < RESERV_FP_SIZE; i++) {
            if (reservFP[i] == NULL) continue;
            if (reservFP[i]->index == oldest_completed_instr->index) {
                reservFP[i] = NULL;
                break;
            }
        }
    }

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
    commonDataBus = NULL;

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
    
    for (int i = 0; i < INSTR_QUEUE_SIZE; i++) {
        if (instr_queue[i] != NULL) return false;
    }

    for (int i = 0; i < RESERV_INT_SIZE; i++) {
        if (reservINT[i] != NULL) return false;
    }

    for (int i = 0; i < RESERV_FP_SIZE; i++) {
        if (reservFP[i] != NULL) return false;
    }

    for (int i = 0; i < FU_INT_SIZE; i++) {
        if (fuINT[i] != NULL) return false;
    }

    for (int i = 0; i < FU_FP_SIZE; i++) {
        if (fuFP[i] != NULL) return false;
    }

    return true;  //ECE552: you can change this as needed; we've added this so the code provided to you compiles
}



void debug_cycle(int cycle);

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
  fetch_index = 1;
  while (true) {
     /* ECE552: YOUR CODE GOES HERE */
    //   fetch(trace, cycle);
                int debug = 0;    
                if(debug) printf("F2D\n");
    fetch_To_dispatch(trace, cycle);
                if(debug) printf("D2I\n");
    dispatch_To_issue(cycle);
                if(debug) printf("I2E\n");
    issue_To_execute(cycle);
                if(debug) printf("E2C\n");
    execute_To_CDB(cycle);
                if(debug) printf("C2R\n");
    CDB_To_retire(cycle);
    
    
    if (is_simulation_done(sim_num_insn)) break;

    if (cycle % 100 == 0){
        //printf("\tID In CDB: %d\n\n", commonDataBus == NULL ? -1 : commonDataBus->index);
        //debug_cycle(cycle);
    }

    cycle++;
  }
  
  return cycle; 
}

void debug_cycle(int cycle) {
    printf("Cycle: %d\n", cycle);

    int i = 0;
    int count = 0;

    for(i = 0; i < INSTR_QUEUE_SIZE; i++) {
        if(instr_queue[i] != NULL) {
            count++;
            printf("\t\tRes INT i: %d index: %d OP: %d\n", i, instr_queue[i]->index, instr_queue[i]->op);
        }
    }
    printf("\tNum In IFQ: %d\n\n", count);
    count = 0;
    for (i = 0; i < RESERV_INT_SIZE; i++) {
        if (reservINT[i] != NULL) {
            count++;
            printf("\t\tRes INT i: %d index: %d OP: %d\n", i, reservINT[i]->index, reservINT[i]->op);
        }
    }
    printf("\tNum In rINT: %d\n", count);
    count = 0;
    for (i = 0; i < RESERV_FP_SIZE; i++) {
        if (reservFP[i] != NULL) count++;
    }
    printf("\tNum In rFP: %d\n\n", count);
    count = 0;
    for (i = 0; i < FU_INT_SIZE; i++) {
        if (fuINT[i] != NULL){
             count++;
            printf("\t\tFU i: %d index: %d\n", i, fuINT[i]->index);
        }
    }
    printf("\tNum In fuINT: %d\n", count);
    count = 0;
    for (i = 0; i < FU_FP_SIZE; i++) {
        if (fuFP[i] != NULL) count++;
    }
    printf("\tNum In fuFP: %d\n\n", count);
    printf("\tID In CDB: %d\n\n", commonDataBus == NULL ? -1 : commonDataBus->index);
    
}
