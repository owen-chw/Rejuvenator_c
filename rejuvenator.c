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
#define N_PHY_BLOCKS    150     //number of physical blocks in disk
#define N_LOG_BLOCKS    100     //number of logical blocks in disk (< N_PHY_BLOCKS)
#define N_PAGE          100     //number of page in a block
#define LRU_SIZE        100     //lru size by page
#define MAX_ERASE_CNT   100     //

int tau = 20;     //max_wear <= min_wear + tau
bool clean[N_PHY_BLOCKS] = {True};  // clean bit for physical block; phy ID -> bool
int index_2_physical[N_PHY_BLOCKS]; // index -> phy ID
int erase_count_index[N_PHY_BLOCKS] = N_PHY_BLOCKS;    //erase count separator; erase count i -> end index of erase cnt=i in index_2_physical array
/*            Rejuvenator index data structure
            index_2_physical : it is index for each physical block 
            erase_count_index : it is seperator to separate each regions with same erase count
            

            index_2_physical: a[1,5,7,3,2]  a[0] means the physical block 1, a[2] means the physical block 7
            erase_count_index: [2,4,5] means a[0:2] have erase count 0
                                             a[2:4] have erase count 1
                                             a[4:5] have erase count 2
            erase count 0: index_2_physical[0,erase_count_index[0])
                        1: index_2_physical[erase_count_index[0],erase_count_index[1])
                        2: index_2_physical[erase_count_index[1],erase_count_index[2])
                        i: index_2_physical[erase_count_index[i-1],erase_count_index[i])
                                            
            erase_count_index: [0,0,0,3,3,5] means a[0:3] have erase count 3
                                                   a[3:5] have erase count 5
            FYI a[x:y] means a[x],a[x+1]....a[y-1]
*/

void initialize(){
    for(int i=0 ; i<N_PHY_BLOCKS ; i++){
        index_2_physical[i] = i;
    }
}
