/************************************************************************************
 * modified rejuvenator in C                                                        *
 * Hong Wen, Chen                                                                   *
 * 2022/07/29                                                                       *
 * page addressing                                                                  *
 * We store logical address info in spare area in this version                      *
 * We replace phy_page_info array with is_valid_page array.                         *
 * / valid                                                                          *
 * \ not valid / clean (active block is not clean)                                  *
 *             \ invalid                                                            *
 * Rule of triggering GC is modified to l_clean_cnt+h_clean_cnt < 1 in this version *
 * In this version, we maintain the invariant of l_clean_cnt + h_clean_cnt >= 1     *
 ***********************************************************************************/

#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <assert.h>

#define CLEAN               (-1)
#define INVALID             (-2)
#define N_PHY_BLOCKS        150     //number of physical blocks in disk
#define N_LOG_BLOCKS        100     //number of logical blocks in disk (< N_PHY_BLOCKS)
#define N_PAGE              100     //number of page in a block
#define LRU_SIZE            100     //lru cache size by page
#define MAX_WEAR_CNT        1000    //user defined constant
#define DATA_MIGRATION_FREQ 100     //data migration frequency: after doing i times of GC, do data_migration once

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

int l_to_p[N_LOG_BLOCKS][N_PAGE];  //page table: [lb][lp] -> physical address(by page addressing); initialize to -1
bool is_valid_page[N_PHY_BLOCKS][N_PAGE];   //show whether this page is valid or not: [pb][pp] -> bool
int spare_area[N_PHY_BLOCKS][N_PAGE];   //to simulate spare area in the disk: [pb][pp] -> logical address ; this is called "phy_page_info_disk_api" in pseudo code

int l_clean_counter; //number of clean blocks in the lower number list
int h_clean_counter;   //number of clean blocks in the higher number list

int cache[LRU_SIZE] = {-1};             //cache of hot/cold data seperation, each element store logical address(page addressing)
bool chance_arr[LRU_SIZE] = {false};     //second chance array of lru cache
int chance_index_p = 0;                 //index pointer in chance_arr
 
//TODO: update tau?
// when to invoke data migration?

/*
* initialize
*/
void initialize(void){
    for(int i=0 ; i<N_PHY_BLOCKS ; i++){
        index_2_physical[i] = i;
        clean[i] = true;
    }

    for(int i=0 ; i<N_LOG_BLOCKS ; i++){
        for(int j=0 ; j<N_PAGE ; j++){
            l_to_p[i][j] = -1;
        }
    }

    for(int i=0 ; i<N_PHY_BLOCKS ; i++){
        for(int j=0 ; j<N_PAGE ; j++){
            is_valid_page[i][j] = false; 
            spare_area[i][j] = -1;
        }
    }

    for(int i=0 ; i<LRU_SIZE ; i++){
        cache[i] = -1;
    }

    for(int i=0 ; i<MAX_WEAR_CNT ; i++){
        erase_count_index[i] = N_PHY_BLOCKS;
    }

    h_act_block_index_p = N_PHY_BLOCKS / 2;
    h_act_page_p = 0;
    l_act_block_index_p = 0;
    l_act_page_p = 0;

    l_clean_counter = N_PHY_BLOCKS / 2; //number of clean blocks in the lower number list
    h_clean_counter = N_PHY_BLOCKS - l_clean_counter;   //number of clean blocks in the higher number list

    //active block is not a clean block
    l_clean_counter -= 1;
    h_clean_counter -= 1;
    clean[l_act_block_index_p] = false;
    clean[h_act_block_index_p] = false;
}

/*
*   read major function
*   :param lb: logical block
*   :param lp: logical page
*   :return: return data in the page
*/
int read(int lb, int lp){
    int pa = l_to_p[lb][lp];    //lookup page table to get physical address (page addressing)
    assert(pa != -1);   //when pa == -1, logical address map to nothing => error
    int pb = pa / N_PAGE;   //get physical block
    int pp = pa % N_PAGE;   //get physical page
    assert(is_valid_page[pb][pp] != false); //check if it is a vlaid page
    int data = _r(pb, pp);  //use api to read from the address
    return data;
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
    write_helper(d, lb, lp);
    update_lru(lb, lp);
    //if there is no clean block then GC
    if (h_clean_counter + l_clean_counter < 1){
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
void write_helper(int d, int lb, int lp){
    //check the logical address is hot or cold
    if( !isHotPage(lb, lp)){
        //cold data
        write_2_higher_number_list(d, lb, lp);
    }else{
        //hot data
        write_2_lower_number_list(d, lb, lp);
    }
}

/*
* helper function of writting to higher num list
*    :param d: data
*    :param lb: logical block address
*    :param lp: logical page number
*    :return:
*/
void write_2_higher_number_list(int d, int lb, int lp){
    //invalidate old physical address
    if(l_to_p[lb][lp] != -1){
        //clean previous physical address from the same logical address
        int old_addr = l_to_p[lb][lp];
        int opb = old_addr / N_PAGE; //turn page addressing to block id
        int opp = old_addr % N_PAGE; //turn page addressing to page offset
        is_valid_page[opb][opp] = false;
        _write_spare_area(opb, opp, -1);
    }

    //write data to new physical address
    int pb = index_2_physical[h_act_block_index_p]; //get active block ID
    int pp = h_act_page_p;  //get active page
    _w(d, pb, pp);  //write data

    //update logical to physical mapping
    int new_addr = pb * N_PAGE + pp;
    l_to_p[lb][lp] = new_addr;
    int la = lb * N_PAGE + lp;
    _write_spare_area(pb, pp, la);
    is_valid_page[pb][pp] = true;

    //update active pointer value
    if(h_act_page_p + 1 == N_PAGE ){
        //page + 1 == block size
        //move the high pointer to the next clean block
        //firstly search a clean block from the head of the high number list
        h_act_page_p = 0;

        h_act_block_index_p = N_PHY_BLOCKS / 2;
        while(clean[index_2_physical[h_act_block_index_p]] == false && h_act_block_index_p < N_PHY_BLOCKS){
            h_act_block_index_p ++;
        }

        //if no clean blocks in higher number list, then search clean block in lower number list
        if(h_act_block_index_p == N_PHY_BLOCKS){
            h_act_block_index_p = 0;
        }
        while(clean[index_2_physical[h_act_block_index_p]] == false && h_act_block_index_p < (N_PHY_BLOCKS / 2)){
            h_act_block_index_p ++;
        }

        if( h_act_block_index_p < (N_PHY_BLOCKS/2) ){
            l_clean_counter -= 1;
        }else{
            h_clean_counter -= 1;
        }

        clean[index_2_physical[h_act_block_index_p]] = false;
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
void write_2_lower_number_list(int d, int lb, int lp){
    // invalidate  old physical address
    if(l_to_p[lb][lp] != -1){
        //clean previous physical address from the same logical address
        int old_addr = l_to_p[lb][lp];
        int opb = old_addr / N_PAGE; //turn page addressing to block id
        int opp = old_addr % N_PAGE; //turn page addressing to page offset
        is_valid_page[opb][opp] = false;
        _write_spare_area(opb, opp, -1);
    }

    //wirte data to new physical address
    int pb = index_2_physical[l_act_block_index_p]; //get active block ID
    int pp = l_act_page_p;  //get active page
    _w(d, pb, pp);  //write data

    //update logical to physical mapping
    int new_addr = pb * N_PAGE + pp;
    l_to_p[lb][lp] = new_addr;
    int la = lb * N_PAGE + lp;
    _write_spare_area(pb, pp, la);
    is_valid_page[pb][pp] = true;

    //update active pointer value
    if (l_act_page_p + 1 == N_PAGE){
        //page + 1 == block size
        //move the low pointer to the next clean block
        //search a clean block from the head of the low number list 
        l_act_page_p = 0;

        // firstly we search clean block in lower number list
        // if we can't find any clean block in lower number list, then we search in higher number list
        l_act_block_index_p = 0;
        while( clean[ index_2_physical[ l_act_block_index_p ] ] == false && l_act_block_index_p < N_PHY_BLOCKS ){
            l_act_block_index_p += 1;
        }       

        if(l_act_block_index_p < (N_PHY_BLOCKS / 2)){
            l_clean_counter -= 1;
        }else{
            h_clean_counter -= 1;
        }

        clean[ index_2_physical[ l_act_block_index_p ] ] = false;
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
        int h_vic_idx = find_vb(N_PHY_BLOCKS/2, N_PHY_BLOCKS);
        erase_block_data(h_vic_idx); 
    }else if(l_clean_counter < 1){
        // check lower number list
        int l_vic_idx = find_vb(0, N_PHY_BLOCKS/2);
        erase_block_data(l_vic_idx);
    }else{
        int v_idx = find_vb(0, N_PHY_BLOCKS);
        erase_block_data(v_idx);
    }

    //invoke data migration after do GC DATA_MIGRATION_FREQ times
    static int GC_counter = 0;
    GC_counter += 1;
    if (GC_counter % DATA_MIGRATION_FREQ == 0){
        data_migration();
    }
}

/*
*perform data migration when victim block is in Maxwear
*/
void data_migration(void){
    int idx = get_most_clean_efficient_block_idx();
     // max_wear may > min_wear+tau after adapting tau
     // max_wear may < min_wear+tau when the rejuvenator just start
    if( min_wear() + tau <= get_erase_count_by_idx(idx) ){     // max_wear may > min_wear+tau after adapting tau
        // move all the block in min_wear
        if(min_wear() == 0){
            idx = 0;
        }else{
            idx = erase_count_index[min_wear() - 1]; // set index to the front of erase count i   
        }
        int end_idx = erase_count_index[ min_wear() ];
        while(idx < end_idx){
            erase_block_data(idx);
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
    return -1;    //hapens when rejuvenator just start, for all i, erase_count_index[i] == N_PHY_Blocks 

}

/*
*    Get the erase count of max_wear value
*    :return: max_wear value; if error, return -1
*/
int max_wear(void){
    for(int i = 0 ; i<MAX_WEAR_CNT ; i++){
        if (erase_count_index[i] == N_PHY_BLOCKS){
            return i;
        }
    }
    return -1;
}

/*
* Get the erase-count of the physical block indexed by idx in the index_2_physical
*    :param idx: index in the index_2_physical
*    :return: erase count
*/
int get_erase_count_by_idx(int idx){
    for(int cur = 0 ; cur < MAX_WEAR_CNT ; cur++){
        if (erase_count_index[cur] > idx){
            return cur;
        }
    }
    return MAX_WEAR_CNT;    
}

/*
*find a victim block from [erase_count_start, erase_count_end)
*    :return victim_idx
*/
int find_vb(int start_idx, int end_idx){
    int idx = start_idx;
    int vic_idx = idx;
    int n_of_max_invalid_or_clean_page = 0;
    
    while(idx != end_idx){
        int pid = index_2_physical[idx]; // get physical block id

        //ignore the block within the list of erase_cnt= (min_wear + tau)
        if(get_erase_count_by_idx(idx) >= min_wear() + tau){
            idx += 1;
            continue;
        }
        //ignore the block indexed by either active pointer
        if (idx == h_act_block_index_p || idx == l_act_block_index_p){
            idx += 1;
            continue;
        }
        //ignore the block with all clean pages
        // this implementation is different from pseudo code
        if(clean[pid] == true){
            idx += 1;
            continue;
        }

        int n_of_invalid_or_clean_page = 0;
        for(int pp = 0 ; pp < N_PAGE ; pp++){
            if(is_valid_page[pid][pp] == false){
                n_of_invalid_or_clean_page +=1;
            }
        }

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
int get_most_clean_efficient_block_idx(void){
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
        if(clean[pid] == true){
            idx += 1;
            continue;
        }

        int n_of_invalid_or_clean_page = 0;
        for(int pp = 0 ; pp < N_PAGE ; pp++){
            if(is_valid_page[pid][pp] == false){
                n_of_invalid_or_clean_page +=1;
            }
        }
                
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
void erase_block_data(int idx){
    int pb = index_2_physical[idx]; //get physical block
    int pp = 0; //get physical page
    
    //copy valid page to another space and set the page to clean
    while(pp != N_PAGE){
        if(is_valid_page[pb][pp]){
            int la = _read_spare_area(pb, pp); //get logical addr
            int lb = la / N_PAGE; //get logical block id
            int lp = la % N_PAGE;   //get logical page offset
            write_helper(_r(pb,pp), lb, lp);
        }
        pp++;
    }
    
    //erase the block by disk erase API
    _erase_block(pb);
    //update block clean status
    clean[pb] = true;

    //update clean counter
    if(idx < (N_PHY_BLOCKS/2) ){
        l_clean_counter += 1;
    }else{
        h_clean_counter += 1;
    }

    //update erase count for pb
    increase_erase_count(idx);
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
void increase_erase_count(int idx){
    //swap the index_2_physical[idx] with the element which has teh same erase count
    int erase_count = get_erase_count_by_idx(idx); //get the erase cnt of idx
    int last_block_idx = erase_count_index[erase_count] - 1;    //get the ending index which has the same erase cnt

    // let active block pointer stay with the same blockID
    if(last_block_idx == h_act_block_index_p){
        h_act_block_index_p = idx;
    }
    if(last_block_idx == l_act_block_index_p){
        l_act_block_index_p = idx;
    }

    //need to check if idx and last_block_idx are clean?
    // if one of them are not clean, then need to update clean counter during swap
    if(clean[index_2_physical[last_block_idx]] == false){
        if(idx < (N_PHY_BLOCKS/2) && last_block_idx >= (N_PHY_BLOCKS/2)){
            l_clean_counter -= 1;
            h_clean_counter += 1;
        }
    }

    int temp = index_2_physical[idx];
    index_2_physical[idx] = index_2_physical[last_block_idx];
    index_2_physical[last_block_idx] = temp;

    // update the erase_count boundary index
    erase_count_index[erase_count] -= 1;
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
*    :return: data in this page
*/
int _r(int pb, int pg){
    //pass
}

/*
*    DISK API
*    read logical page info from the space area
*    :param pb: physical block address
*    :param pp: physical page address
*    :return logical address: 
*/
int _read_spare_area(int pb, int pp){
    return spare_area[pb][pp];
}

/*
*    DISK API
*    write logical page info into the space area
*    :param pb: physical block address
*    :param pp: physical page address
*    :param la: logical address
*/
void _write_spare_area(int pb, int pp, int la){
    spare_area[pb][pp] = la;
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
*   update lru_cache after write
*   :param lb: logical block ID
*   :param lp: logical page offset
*   :return:
*/
void update_lru(int lb, int lp){
    int la = lb * N_PAGE + lp;  //get locical address (page addressing)
    int exist = find_and_update(la);    //check whether la in cache or not
    if(!exist){
        replace_and_update(la);     //if la is not in cache, then update cache
    } 
}

/*
*   check whether logical addr la in cache
*   :param la: logical address
*   :return: if la in cache, then return true; else return false
*/
bool find_and_update(int la){
    for(int i=0 ; i<LRU_SIZE ; i++){
        if(cache[i] == la){
            chance_arr[i] = true;
            return true;
        }
    }
    return false;
}

/*  find an entry of no chance, replace it with la, update chance_arr
*   :param la: logical address
*   :return:
*/
void replace_and_update(int la){
    while(1){
        if(chance_arr[chance_index_p] == false){
            cache[chance_index_p] = la;
            chance_index_p = (chance_index_p + 1) % LRU_SIZE;
            return;
        }else{
            chance_arr[chance_index_p] = false;
            chance_index_p = (chance_index_p + 1) % LRU_SIZE;
        }
    }
}

/*
*   if la is in cache, la is a hot page
*   :param lb: logical block
*   :param lp: logical page
*   :return: if la is in cache, then return true
*/
bool isHotPage(int lb, int lp){
    int la = lb * N_PAGE + lp;  //get logical address (page addressing)
    // currently brute force, traverse cache once
    for(int i=0 ; i<LRU_SIZE ; i++){
        if(cache[i] == la){
            return true;
        }
    }
    return false;
}

int main(void){
    initialize();
}
