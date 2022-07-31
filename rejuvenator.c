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

//TODO: init_LRU_cache, updata_lru, is hot page, read, update tau?

/*
* initialize
*/
void initialize(void){
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
        h_clean_counter -= 1;
        clean[index_2_physical[h_act_block_index_p]] = false;
        h_act_page_p = 0;

        h_act_block_index_p = N_PHY_BLOCKS / 2;
        while(clean[index_2_physical[h_act_block_index_p]] == false && h_act_block_index_p < N_PHY_BLOCKS){
            h_act_block_index_p ++;
        }
    }else{
        //page + 1 < block size
        h_act_page_p +=1;
    }
}

/*
* helper function of writting to lower num list
*    :param d: data
*    :param lb: logical block address
*    :param lp: logical page number
*    :return:
*/
void _write_2_lower_number_list(int d, int lb, int lp){
    int pb = index_2_physical[l_act_block_index_p]; //get active block ID
    int pp = l_act_page_p;  //get active page
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
    if (l_act_page_p + 1 == N_PAGE){
        //page + 1 == block size
        //move the low pointer to the next clean block
        //search a clean block from the head of the low number list 
        l_clean_counter -= 1;
        clean[ index_2_physical[ l_act_block_index_p ] ] = false;
        l_act_page_p = 0;

        l_act_block_index_p = 0;
        while( clean[ index_2_physical[ l_act_block_index_p ] ] == false && l_act_block_index_p < (N_PHY_BLOCKS / 2) ){
            l_act_block_index_p += 1;
        }       
    }else{
        //page + 1 < block size
        l_act_page_p += 1;
    }
}

/*
*perform garbage collection to ensure there is at least one clean block
*    :return:
*/
void gc(void){
    //first check higher number list to guarantee the invariant of h_clean_counter >= 1
    if(h_clean_counter < 1){
        int h_vic_idx = _find_vb(N_PHY_BLOCKS/2, N_PHY_BLOCKS);
        _erase_block_data(h_vic_idx); 
    }else if(l_clean_counter < 1){
        // check lower number list
        int l_vic_idx = _find_vb(0, N_PHY_BLOCKS/2);
        _erase_block_data(l_vic_idx);
    }else{
        int v_idx = _find_vb(0, N_PHY_BLOCKS);
        _erase_block_data(v_idx);
    }
}

/*
*perform data migration when victim block is in Maxwear
*/
void data_migration(void){
    int idx = _get_most_clean_efficient_block_idx();
    if( min_wear() + tau <= _get_erase_count_by_idx(idx) ){     //why don't use max_wear() ? why < ?
        // move all the block in min_wear
        idx = erase_count_index[ min_wear() - 1 ];  //set index to the front of erase count i   //if min_wear()=0 ?
        int end_idx = erase_count_index[ min_wear() ];
        while(idx < end_idx){
            _erase_block_data(idx);
            idx +=1;
        }
    } 
}

/*
* get the erase count of min wear
*   :return: min_wear value
*/  
int min_wear(void){
    for (int i=0 ; i<MAX_WEAR_CNT ; i++){
        if(erase_count_index[i] != 0){
            return i;
        }
    }
    return N_PHY_BLOCKS;    //why?

}

/*
*    Get the erase count of max_wear value
*    :return: max_wear value
*/
int max_wear(void){
    for(int i = 0 ; i<MAX_WEAR_CNT ; i++){
        if (erase_count_index[i] == N_PHY_BLOCKS){
            return i;
        }
    }
}

/*
* Get the erase-count of the physical block indexed by idx in the index_2_physical
*    :param idx: index in the index_2_physical
*    :return: erase count
*/
int _get_erase_count_by_idx(int idx){
    for(int cur = 0 ; cur < N_PHY_BLOCKS ; cur++){
        if (erase_count_index[cur] > idx){
            return cur;
        }
    }
    return N_PHY_BLOCKS;    //why?
}
/*
*find a victim block from [erase_count_start, erase_count_end)
*    :return victim_idx
*/
int _find_vb(int start_idx, int end_idx){
    int idx = start_idx;
    int vic_idx = idx;
    int n_of_max_invalid_or_clean_page = 0;
    
    while(idx != end_idx){
        int pid = index_2_physical[idx]; // get physical block id

        //ignore the block within the list of erase_cnt= (min_wear + tau)
        if(_get_erase_count_by_idx(idx) >= min_wear() + tau){
            continue;
        }
        //ignore the block indexed by either active pointer
        if (idx == h_act_block_index_p || idx == l_act_block_index_p){
            continue;
        }
        //ignore the block with all clean pages
        // this implementation is different from pseudo code
        int clean_page_counter = 0;
        int invalid_page_counter = 0;
        for(int pp = 0 ; pp < N_PAGE ; pp++){
            if (phy_page_info[pid][pp] == CLEAN){
                clean_page_counter ++;
            }else if(phy_page_info[pid][pp] ==  INVALID){
                invalid_page_counter ++;
            }
        }
        if (clean_page_counter == N_PAGE){
            //ignore the block with all clean pages
            continue;
        }
        int n_of_invalid_or_clean_page = clean_page_counter + invalid_page_counter;
        if(n_of_invalid_or_clean_page >= n_of_max_invalid_or_clean_page){
            vic_idx = idx;
            n_of_max_invalid_or_clean_page = n_of_invalid_or_clean_page;
        }
        idx++;
    }
    return vic_idx;
}

/*
* this is similiar with _find_vb
* but it doesn't ignore blocks in Maxwear
*   :return: most_clean_efficient_idx
*/ 
int _get_most_clean_efficient_block_idx(void){
    int most_efficient_idx = 0;
    int n_of_max_invalid_or_clean_page = 0;

    for(int idx = 0 ; idx < N_PHY_BLOCKS ; idx++){
        int pid = index_2_physical[idx];    // get physical block id

         //ignore the block indexed by either active pointer
        if (idx == h_act_block_index_p || idx == l_act_block_index_p){
            continue;
        }
        //ignore the block with all clean pages
        // this implementation is different from pseudo code
        int clean_page_counter = 0;
        int invalid_page_counter = 0;
        for(int pp = 0 ; pp < N_PAGE ; pp++){
            if (phy_page_info[pid][pp] == CLEAN){
                clean_page_counter ++;
            }else if(phy_page_info[pid][pp] ==  INVALID){
                invalid_page_counter ++;
            }
        }       
        if (clean_page_counter == N_PAGE){
            //ignore the block with all clean pages
            continue;
        }
        int n_of_invalid_or_clean_page = clean_page_counter + invalid_page_counter;
        if(n_of_invalid_or_clean_page >= n_of_max_invalid_or_clean_page){
            most_efficient_idx = idx;
            n_of_max_invalid_or_clean_page = n_of_invalid_or_clean_page;
        }
    }
    return most_efficient_idx;
}

/*
* move valid page and erase this block; then increase erase cnt
*   :param idx: index in the index_2_physical
*   :return:
*/
void _erase_block_data(int idx){
    int pb = index_2_physical[idx]; //get physical block
    int pp = 0; //get physical page
    
    //copy valid page to another space and set the page to clean
    while(pp != N_PAGE){
        if(phy_page_info[pb][pp] >= 0){
            int la = phy_page_info[pb][pp]; //get logical addr
            int lb = la / N_PAGE; //get logical block id
            int lp = la % N_PAGE;   //get logical page offset
            _write_helper(_r(pb,pp), lb, lp);
        }
        phy_page_info[pb][pp] = CLEAN;
        pp++;
    }
    
    //erase the block by disk erase API
    _erase_block(pb);
    //update erase count for pb
    _increase_erase_count(idx);
}

/*
* increase the erase count by swapping idx with the last elment which has the same erase count
*   :param idx: index in the index_2_physical
*   :return:
**********************************************************************************************
a  example of FTLEraseOneBlock:
    index                          : 0, 1, 2, 3, 4, 5, 6
	erase count                    : 1, 2, 2, 2, 2, 3, 4
	index_2_physical store block ID: 1, 3, 2, 4, 5, 6, 7

	now we want to erase idx = 2;
	get its erase count:
		erase_count = _get_erase_count_by_idx(idx) = 2
	get the end index of the same "old erasecnt" in the index_2_physical:
		last_block_idx = erase_count_index[erase_count] - 1 = 5-1 = 4
	swap the block of index=2 and index=4 in index_2_physical, then get:
	index                          : 0, 1, 2, 3, 4, 5, 6
	erase count                    : 1, 2, 2, 2, 2, 3, 4
	index_2_physical store block ID: 1, 3, 5, 4, 2, 6, 7

	update erase count boundry:
        erase_count_index[erase_count] -=1  5->4
	index                          : 0, 1, 2, 3, 4, 5, 6
	erase count                    : 1, 2, 2, 2, 3, 3, 4
	index_2_physical store block ID: 1, 3, 5, 4, 2, 6, 7
*/
void _increase_erase_count(int idx){
    //swap the index_2_physical[idx] with the element which has teh same erase count
    int erase_count = _get_erase_count_by_idx(idx); //get the erase cnt of idx
    int last_block_idx = erase_count_index[erase_count] - 1;    //get the ending index which has the same erase cnt
    int temp = index_2_physical[idx];
    index_2_physical[idx] = index_2_physical[last_block_idx];
    index_2_physical[last_block_idx] = temp;

    // update the erase_count boundary index
    erase_count_index[erase_count] -= 1;

    idx = last_block_idx;   // because the block ID in old idx is now in last_block_idx
    //update clean counter
    if(idx < (N_PHY_BLOCKS/2)){
        l_clean_counter += 1;
    }else{
        h_clean_counter += 1;
    }
}

/*
*    API
*    write data to physical address
*    :param d: data
*    :param pb: physical block
*    :param pg: physical page
*    :return:
*/
void _w(int d, int pb, int pg){
    //pass
}

/*
*    API
*    read from physical block address and page number
*    :param pb: physical block address
*    :param pg: physical page number
*    :return:
*/
int _r(int pb, int pg){
    //pass
}

/*
*    API 
*    erase block
*    :param pb: physical block address
*    :return:
*/
void _erase_block(int pb){
    //pass
}

/*
*    Get the head index of the erase-count in the index_2_physical
*    :param erase_count: erase count i
*    :return: the head index of erase_cnt=i in the index_2_physical
*               if erase_cnt=i is an empty list, then return -1
*/
int _get_head_idx(int erase_count){
    if(erase_count == 0){
        return 0;
    }else{
        if(erase_count_index[erase_count - 1] >= erase_count_index[erase_count]){
            //erase_count = i is an empty list, no head
            return -1;
        }else{
            return erase_count_index[erase_count - 1];
        }
    }
}

void _update_lru(int lb, int lp){

}

bool isHotPage(int lb, int lp){

}

int main(void){
    initialize();
}
