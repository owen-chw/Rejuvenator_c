/*****************************
 * modified rejuvenator in C *
 * Hong Wen, Chen            *
 * 2022/07/29                *
 * page addressing           *
 ****************************/

#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>

#define CLEAN           (-1)
#define INVALID         (-2)
#define N_PHY_BLOCKS    150     //number of physical blocks in disk
#define N_LOG_BLOCKS    100     //number of logical blocks in disk (< N_PHY_BLOCKS)
#define N_PAGE          100     //number of page in a block
#define LRU_SIZE        100     //lru size by page
#define MAX_WEAR_CNT    1000     //user defined constant

int tau = 20;     //max_wear <= min_wear + tau
bool clean[N_PHY_BLOCKS] = {true};  // clean bit for physical block; phy block ID -> bool
int index_2_physical[N_PHY_BLOCKS]; //main list of rejuvenator; index -> phy block ID
int erase_count_index[MAX_WEAR_CNT] = {N_PHY_BLOCKS};    //erase count separator; erase count i -> end index of erase cnt=i in index_2_physical array

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
int h_act_block_index_p = N_PHY_BLOCKS / 2;      // high active block pointer based on index_2_physical
int h_act_page_p = 0;   //high active page pointer for physical page
int l_act_block_index_p = 0;    //low active block pointer based on index_2_physical
int l_act_page_p = 0;   //low active page pointer for physical page

int l_to_p[N_LOG_BLOCKS][N_PAGE] = {-1};  //page table: [lb][lp] -> physical address(by page addressing)
int phy_page_info[N_PHY_BLOCKS][N_PAGE] = {CLEAN};  //page information it can be INVALID, CLEAN, or int: logical address (by page addressing)

int l_clean_counter; //number of clean blocks in the lower number list
int h_clean_counter;   //number of clean blocks in the higher number list

//TODO: LRU cache

/*
* initialize
*/
void initialize(){
    for(int i=0 ; i<N_PHY_BLOCKS ; i++){
        index_2_physical[i] = i;
    }
    l_clean_counter = N_PHY_BLOCKS / 2; //number of clean blocks in the lower number list
    h_clean_counter = N_PHY_BLOCKS - l_clean_counter;   //number of clean blocks in the higher number list
}

/*
* write major function
*    :param d: data
*    :param lb: logical block
*    :param lp: logical page
*   invariant: h_clean_counter >= 1
*/
void write(int d, int lb, int lp)
{
    _write_helper(d, lb, lp);
    _update_lru(lb, lp);
    //if there is no clean block then GC
    if (h_clean_counter < 1){
        gc();
    }
}

/*
* write helper function
*    :param d: data
*    :param lb: logical block address
*    :param lp: logical page number
*    :return:
*/
void _write_helper(int d, int lb, int lp){
    //check the logical address is hot or cold
    if( !isHotPage(lb, lp)){
        //cold data
        _write_2_higher_number_list(d, lb, lp);
    }else{
        //hot data
        if(l_clean_counter < 1){
            //if there is no clean block in the lower number list, write to the higher number list
            _write_2_higher_number_list(d, lb, lp);
        }else{
            //write to lower number list
            _write_2_lower_number_list(d, lb, lp);
        }
    }
}

/*
* helper function of writting to higher num list
*    :param d: data
*    :param lb: logical block address
*    :param lp: logical page number
*    :return:
*/
void _write_2_higher_number_list(int d, int lb, int lp){
    int pb = index_2_physical[h_act_block_index_p]; //get active block ID
    int pp = h_act_page_p;  //get active page
    _w(d, pb, pp);  //write data

    //update logical to physical mapping
    if(l_to_p[lb][lp] != -1){
        //clean previous physical address from the same logical address
        int old_addr = l_to_p[lb][lp];
        int opb = old_addr / N_PAGE; //turn page addressing to block id
        int opp = old_addr % N_PAGE; //turn page addressing to page offset
        phy_page_info[opb][opp] = INVALID;
    }
    int new_addr = pb * N_PAGE + pp;
    l_to_p[lb][lp] = new_addr;

    //update active pointer value
    if(h_act_page_p + 1 == N_PAGE ){
        //page + 1 == block size
        //move the high pointer to the next clean block
        //search a clean block from the head of the high number list
        h_act_block_index_p = N_PHY_BLOCKS / 2;
        while(clean[index_2_physical[h_act_block_index_p]] == false){
            h_act_block_index_p ++;
        }
        h_clean_counter -= 1;
        clean[index_2_physical[h_act_block_index_p]] = false;
        h_act_page_p = 0;
    }else{
        //page + 1 < block size
        h_act_page_p +=1;
    }
}

void _write_2_lower_number_list(int d, int lb, int lp){

}

void _w(int d, int pb, int pg){

}
void _update_lru(int lb, int lp){

}

bool isHotPage(int lb, int lp){

}

int main(){
    initialize();
}
