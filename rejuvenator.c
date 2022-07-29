/*****************************
 * modified rejuvenator in C *
 * Hong Wen, Chen            *
 * 2022/07/29                *
 * page addressing           *
 ****************************/

#include <stdio.h>
#include <stdlib.h>

#define CLEAN           (-1)
#define INVALID         (-2)
#define N_PHY_BLOCKS    150   //number of physical blocks in disk
#define N_LOG_BLOCKS    100   //number of logical blocks in disk (< N_PHY_BLOCKS)
#define N_PAGE          100   //number of page in a block
#define LRU_SIZE        100
#define MAX_ERASE_CNT   100   //