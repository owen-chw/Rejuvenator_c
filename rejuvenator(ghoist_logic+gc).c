/************************************************************************************
 * modified rejuvenator in C                                                        *
 * Hong Wen, Chen                                                                   *
 * 2022/07/29                                                                       *
 * page addressing                                                                  *
 * We store logical address info in spare area in this version                      *
 * We replace phy_page_info array with is_valid_page array.                         *
 * / valid                                                                          *
 * \ not valid / clean  (active block is not clean)                                                              *
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

void write(int d, int lb, int lp);
int isHotPage(int lb, int lp);
void write_helper(int d, int lb, int lp);
void update_lru(int lb, int lp);
void write_2_higher_number_list(int d, int lb, int lp);
void gc(void);
void _w(int d, int pb, int pg);
void write_2_lower_number_list(int d, int lb, int lp);
int find_vb(int start_idx, int end_idx);
void _erase_block(int pb);
void erase_block_data(int idx);
int get_most_clean_efficient_block_idx(void);
int read(int lb, int lp);
int get_erase_count_by_idx(int idx);
int min_wear(void);
int max_wear(void);
int _r(int pb, int pg);
void increase_erase_count(int idx);
int find_and_update(int la);
void replace_and_update(int la);
void _write_spare_area(int pb, int pp, int la);
int _read_spare_area(int pb, int pp);
void data_migration(void);
//void count_clean_array(int begin, int end);



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
int h_act_block_index_p ;      // high active block pointer based on index_2_physical
int h_act_page_p  ;   //high active page pointer for physical page
int l_act_block_index_p ;    //low active block pointer based on index_2_physical
int l_act_page_p  ;   //low active page pointer for physical page

int l_to_p[N_LOG_BLOCKS][N_PAGE];  //page table: [lb][lp] -> physical address(by page addressing); initialize to -1
bool is_valid_page[N_PHY_BLOCKS][N_PAGE];   //show whether this page is valid or not: [pb][pp] -> bool
int spare_area[N_PHY_BLOCKS][N_PAGE];   //to simulate spare area in the disk: [pb][pp] -> logical address ; this is called "phy_page_info_disk_api" in pseudo code
int disk[N_PHY_BLOCKS][N_PAGE];     // to simulate physical disk: [pb][pp] -> data in the page


int clean_counter;
//int l_clean_counter; //number of clean blocks in the lower number list
//int h_clean_counter;   //number of clean blocks in the higher number list
//int low_array_counter;
//int high_array_counter;

int cache[LRU_SIZE] = {-1};             //cache of hot/cold data seperation, each element store logical address(page addressing)
bool chance_arr[LRU_SIZE] = {false};     //second chance array of lru cache
int chance_index_p = 0;                 //index pointer in chance_arr

//some parameters for testing

 
//TODO: update tau?
// when to invoke data migration?

/*@
    predicate in_L_range(integer lb, integer lp )=
        0 <= lb < N_LOG_BLOCKS && 0 <= lp < N_PAGE;

    predicate in_P_range(integer pb, integer pp )=
        0 <= pb < N_PHY_BLOCKS && 0 <= pp < N_PAGE;
    
    predicate unique{L}(int arr[N_PHY_BLOCKS]) =
        \forall integer i,j; 0 <= i < j < N_PHY_BLOCKS ==> arr[i] != arr[j];
    
    logic integer count_clean(integer idx) = 
        idx<=0 ? 0 :
            (clean[idx-1]==true ? count_clean(idx-1) + 1 : count_clean(idx-1));
    
    logic integer count_efficiency(integer block, integer page) = 
        page<=0 ? 0 :
            (is_valid_page[block][page-1]==false ? count_efficiency(block, page-1)+1 : count_efficiency(block, page-1));

*/


/*@ ghost
    int ghost_logical[N_LOG_BLOCKS][N_PAGE];
*/
/*@ ghost
    int l_array_counter;
 */

/*
    logic integer count_clean(integer begin, integer end)=
        begin >= end ? 0 : (clean[begin]==true) ? count_clean(begin+1, end)+1 : count_clean(begin+1, end);
*/
/*@
    axiomatic Count_Clean{
        logic integer count_clean(integer begin, integer end)
            reads clean[begin .. end-1];

        axiom out_of_range:
            \forall integer begin, end;
                begin >= end ==> count_clean(begin, end) == 0;
        
        axiom is_clean:
            \forall integer begin, end;
                (begin < end && clean[begin] == true) ==>
                    count_clean(begin, end) == 1 + count_clean(begin+1, end);

        axiom not_clean:
            \forall integer begin, end;
                (begin < end && clean[begin] != true) ==>
                    count_clean(begin, end) == count_clean(begin+1, end);
    }
*/

/*@
    requires N_PHY_BLOCKS > begin >= 0;
    requires N_PHY_BLOCKS >= end >= 0;
    requires begin <= end;
    assigns \nothing;
    ensures \result == count_clean(begin, end);
 */
size_t occurrences_of(int begin, int end)
{
    size_t result = 0;

    /*@
        loop invariant begin <= i <= end;
        loop invariant 0 <= result;
        loop invariant  result <= i-begin;
        loop invariant result == count_clean(begin, i);
        loop assigns i, result;
        loop variant end-i;
    */
    for (size_t i = begin; i < end; ++i){
        result += (clean[i] == true) ? 1 : 0;
    }
    return result;
}


/*
* initialize
*/

 
/*@
    ensures in_P_range(h_act_block_index_p, h_act_page_p);
    ensures in_P_range(l_act_block_index_p, l_act_page_p);
    ensures  (  1 <= clean_counter <= N_PHY_BLOCKS );
    ensures \forall  int i,j; 0 <= i < N_LOG_BLOCKS &&  0 <= j < N_PAGE ==>   l_to_p[i][j] == -1;
    ensures  0 <=  chance_index_p < LRU_SIZE;
    ensures 0 <= index_2_physical[h_act_block_index_p] < N_PHY_BLOCKS ;
    ensures \forall integer i; 0 <= i < N_PHY_BLOCKS ==> 0 <= index_2_physical[i] < N_PHY_BLOCKS;
    ensures clean_counter == count_clean( 0, N_PHY_BLOCKS);
    ensures count_clean( 0, N_PHY_BLOCKS / 2 ) == N_PHY_BLOCKS/2 - 1;
    ensures 0 <= tau <= MAX_WEAR_CNT;
    
 */
void initialize(void){
    clean_counter = 0;

    /*@
        loop invariant 0 <= i <= N_PHY_BLOCKS;
        loop invariant \forall integer j; 0 <= j < i ==> clean[j] ==true;
        loop invariant 0 <= i <= N_PHY_BLOCKS ==> clean_counter == count_clean(0, i);
        loop assigns i, clean_counter;

    */
    for(int i=0 ; i<N_PHY_BLOCKS ; i++){
        index_2_physical[i] = i;
        clean[i] = true;
        clean_counter += 1;
    }

    for(int i=0 ; i<N_LOG_BLOCKS ; i++){
        for(int j=0 ; j<N_PAGE ; j++){
            l_to_p[i][j] = -1;
        }
    }

    for(int i=0 ; i<N_PHY_BLOCKS ; i++){
        for(int j=0 ; j<N_PAGE ; j++){
            is_valid_page[i][j] = false;
            //spare_area[i][j] = -1;
        }
    }
    //initialize lru
    for (int i=0; i<LRU_SIZE; i++) {
        cache[i] = -1;
    }
        
        
    for (int i = 0 ; i < MAX_WEAR_CNT; i++) {
        erase_count_index[i] = N_PHY_BLOCKS ;
    }
    
    h_act_block_index_p = N_PHY_BLOCKS / 2;// initialize h_act_block_index_p
    h_act_page_p = 0;
    l_act_block_index_p = 0;   //initialoze l_act_block_index_p
    l_act_page_p = 0;

   // l_clean_counter = N_PHY_BLOCKS / 2; //number of clean blocks in the lower number list
   // h_clean_counter = N_PHY_BLOCKS - l_clean_counter;   //number of clean blocks in the higher number list

    //active block is not a clean block
    clean_counter -= 2;
    clean[l_act_block_index_p] = false;
    clean[h_act_block_index_p] = false;
    
    //count_clean_array(0,N_PHY_BLOCKS/2);
    
            
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
/*@
    requires unique(index_2_physical);
    requires in_L_range(lb, lp);
    requires 1 <= clean_counter <= N_PHY_BLOCKS;
    requires clean_counter == count_clean(N_PHY_BLOCKS);
    requires clean_counter < N_PHY_BLOCKS - 2 ==> 
        (\exists integer i; 0 <= i < N_PHY_BLOCKS && i!=h_act_block_index_p && i!=l_act_block_index_p && clean[index_2_physical[i]]!=true);
    requires in_P_range(h_act_block_index_p, h_act_page_p);
    requires in_P_range(l_act_block_index_p, l_act_page_p);
    requires 0 <= l_to_p[lb][lp] < N_PHY_BLOCKS * N_PAGE || l_to_p[lb][lp] == -1;
    requires -2147483648 <= d <= 2147483647 ;
    requires 0 <=  chance_index_p < LRU_SIZE;
    requires 0 <= index_2_physical[h_act_block_index_p] < N_PHY_BLOCKS ;
    requires \forall integer i; 0 <= i < N_PHY_BLOCKS ==> 0 <= index_2_physical[i] < N_PHY_BLOCKS;
    requires \forall integer i; 0 <= i < MAX_WEAR_CNT ==> erase_count_index[i] <= N_PHY_BLOCKS;
    requires 0 <= l_array_counter < N_PHY_BLOCKS/2;
    requires 0 <= tau <= MAX_WEAR_CNT;
    
    assigns ghost_logical[lb][lp];  
    assigns clean_counter;
    assigns h_act_block_index_p, l_act_block_index_p;
    assigns h_act_page_p, l_act_page_p ;
    assigns erase_count_index[0..(MAX_WEAR_CNT-1)];
    assigns index_2_physical[0..(N_PHY_BLOCKS-1)];
    assigns l_to_p[0..(N_LOG_BLOCKS - 1)][0..(N_PAGE)] ;  
    assigns clean[0..(N_PHY_BLOCKS - 1)];
    assigns spare_area[0..(N_PHY_BLOCKS - 1)][0..(N_PAGE-1)];
    assigns disk[0..(N_PHY_BLOCKS - 1)][0..(N_PAGE-1)];
    assigns is_valid_page[0..(N_PHY_BLOCKS - 1)][0..(N_PAGE-1)];
    
    ensures unique(index_2_physical);
    ensures 0 <= tau <= MAX_WEAR_CNT;
    ensures ghost_logical[lb][lp] == d;
    ensures \forall integer i; 0 <= i < N_PHY_BLOCKS ==> 0 <= index_2_physical[i] < N_PHY_BLOCKS;
    ensures \forall integer i; 0 <= i < MAX_WEAR_CNT ==> erase_count_index[i] <= N_PHY_BLOCKS;
    ensures disk[(l_to_p[lb][lp] / N_PAGE)][(l_to_p[lb][lp] % N_PAGE)] ==d ;
    ensures 0 <= l_to_p[lb][lp] < N_PHY_BLOCKS*N_PAGE || l_to_p[lb][lp] == -1;
    ensures 2 <= clean_counter <= N_PHY_BLOCKS - 2;
    ensures clean_counter == count_clean(N_PHY_BLOCKS);
    ensures clean_counter < N_PHY_BLOCKS - 2 ==>
        (\exists integer i; 0 <= i < N_PHY_BLOCKS && i!=h_act_block_index_p && i!=l_act_block_index_p && clean[index_2_physical[i]]!=true);
    ensures disk[(l_to_p[lb][lp] / N_PAGE)][(l_to_p[lb][lp] % N_PAGE)] == ghost_logical[lb][lp] ;
*/
// todo: for all other place in disk / use assign
void write(int d, int lb, int lp)
{
    
    /*@ ghost
         ghost_logical[lb][lp] = d;
     */
    //@ assert ghost_logical[lb][lp] == d;
    write_helper(d, lb, lp);
    
    //update_lru(lb, lp);
    
     //if there is no clean block then GC
    if (clean_counter < 2){
        //@ assert clean_counter == count_clean(N_PHY_BLOCKS) == 1;
        gc();
    }
    
}

/*
* write helper function
*    :param d: data
*    :param lb: logical block address
*    :param lp: logical page number
*    :return:

NEED TO DO:
Requires: variable_in_range();  //use predicate

Requires: forall lb1, lp1 . Ghost_disk[lb1][lp1] = Disk[l2p_b(lb1) ][ l2p_p(lp1)]
Ensures: forall lb1, lp1 . Ghost_disk[lb1][lp1] = Disk[l2p_b(lb1) ][ l2p_p(lp1)]
Ensures: Ghost_disk[lb][lp] =d  //done
Ensures: forall lb1, lp1 .  lb1!=lb \/ lp1!=lp.   Ghost_disk[lb1][lp1] = \old(Ghost_disk[lb1][lp1])    //maybe use behavior to divide write_2_high/low

Ensures: Ghost_disk[lb][lp] =d = Disk[l2p_b(lb) ][ l2p_p(lp)]
*/
/*@
    requires in_L_range(lb, lp);
    requires in_P_range(h_act_block_index_p, h_act_page_p);
    requires in_P_range(l_act_block_index_p, l_act_page_p);
    requires 0 <= l_to_p[lb][lp] < N_PHY_BLOCKS * N_PAGE || l_to_p[lb][lp] == -1;
    requires  (  1 <= clean_counter <= N_PHY_BLOCKS );
    requires ghost_logical[lb][lp] == d;
    requires 0 <= index_2_physical[h_act_block_index_p] < N_PHY_BLOCKS ;
    requires \forall integer i; 0 <= i < N_PHY_BLOCKS ==> 0 <= index_2_physical[i] < N_PHY_BLOCKS;
    requires 0 <= l_array_counter < N_PHY_BLOCKS/2;
    requires -2147483648 <= d <= 2147483647 ;

    assigns clean_counter;
    assigns h_act_page_p, l_act_page_p ;
    assigns h_act_block_index_p, l_act_block_index_p ;
    assigns clean[0..(N_PHY_BLOCKS - 1)];
    assigns l_to_p[lb][lp];
    assigns spare_area[ index_2_physical[\old(h_act_block_index_p)] ][\old(h_act_page_p)];
    assigns spare_area[ index_2_physical[\old(l_act_block_index_p)] ][\old(l_act_page_p)];
    assigns disk[ index_2_physical[\old(h_act_block_index_p)] ][\old(h_act_page_p)];
    assigns disk[ index_2_physical[\old(l_act_block_index_p)] ][\old(l_act_page_p)];
    assigns is_valid_page[\old(l_to_p[lb][lp])/N_PAGE][\old(l_to_p[lb][lp]) % N_PAGE] ;
    assigns is_valid_page[ index_2_physical[\old(h_act_block_index_p)] ][\old(h_act_page_p)];
    assigns is_valid_page[ index_2_physical[\old(l_act_block_index_p)] ][\old(l_act_page_p)];

    ensures disk[(l_to_p[lb][lp] / N_PAGE)][(l_to_p[lb][lp] % N_PAGE)] == ghost_logical[lb][lp];
    ensures 0 <= l_to_p[lb][lp] < N_PHY_BLOCKS*N_PAGE;
    ensures 0 <= clean_counter <= N_PHY_BLOCKS ;
    ensures ghost_logical[lb][lp] == d;
    ensures disk[(l_to_p[lb][lp] / N_PAGE)][(l_to_p[lb][lp] % N_PAGE)] == d;
    ensures in_P_range(h_act_block_index_p, h_act_page_p);
    ensures in_P_range(l_act_block_index_p, l_act_page_p);
    ensures \forall int lb1,int lp1; ( lb1 != lb || lp1 != lp) && (\old(l_to_p[lb1][lp1]) != -1) && (l_to_p[lb1][lp1] != -1)  ==>   disk[(l_to_p[lb1][lp1] / N_PAGE)][(l_to_p[lb1][lp1] % N_PAGE)] == \old(disk[(l_to_p[lb1][lp1] / N_PAGE)][(l_to_p[lb1][lp1] % N_PAGE)]);
    
*/
void write_helper(int d, int lb, int lp){
    
    //check the logical address is hot or cold
    //@ assert ghost_logical[lb][lp] == d;
    int isHot = isHotPage(lb, lp);
    //@ assert ghost_logical[lb][lp] == d;
    if( isHot != 1){
        //cold data
        //@ assert ghost_logical[lb][lp] == d;
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
245    assigns is_valid_page[ l_to_p[lb][lp] / N_PAGE ][ l_to_p[lb][lp] % N_PAGE ];
246    assigns disk[(l_to_p[lb][lp] / N_PAGE)][(l_to_p[lb][lp] % N_PAGE)];
247    assigns spare_area[ l_to_p[lb][lp] / N_PAGE ][ l_to_p[lb][lp] % N_PAGE ];
    assigns clean[index_2_physical[h_act_block_index_p]];
*/
/*@
    requires in_L_range(lb, lp);
    requires in_P_range(h_act_block_index_p, h_act_page_p);
    requires \valid(clean+(0.. N_PHY_BLOCKS-1));
    requires -2147483648 <= d <= 2147483647 ;
    requires 0 <= l_to_p[lb][lp] < N_PHY_BLOCKS * N_PAGE || l_to_p[lb][lp] == -1;
    requires ghost_logical[lb][lp] == d;
    requires 1 <= clean_counter <= N_PHY_BLOCKS ;
    requires 0 <= index_2_physical[h_act_block_index_p] < N_PHY_BLOCKS ;
    requires \forall integer i; 0 <= i < N_PHY_BLOCKS ==> 0 <= index_2_physical[i] < N_PHY_BLOCKS;

    assigns l_to_p[lb][lp] ;
    assigns is_valid_page[\old(l_to_p[lb][lp])/N_PAGE][\old(l_to_p[lb][lp]) % N_PAGE] ;
    assigns is_valid_page[ index_2_physical[\old(h_act_block_index_p)] ][\old(h_act_page_p)];
    assigns disk[ index_2_physical[\old(h_act_block_index_p)] ][\old(h_act_page_p)];
    assigns spare_area[ index_2_physical[\old(h_act_block_index_p)] ][\old(h_act_page_p)];
    assigns h_act_page_p ;
    assigns h_act_block_index_p ;
    assigns clean_counter;
    assigns clean[0..(N_PHY_BLOCKS - 1)];

    ensures ( \old(l_to_p[lb][lp]) != -1 ) && (\old(l_to_p[lb][lp]) / N_PAGE != \old(index_2_physical[\old(h_act_block_index_p)])) && (\old(l_to_p[lb][lp]) % N_PAGE != \old(h_act_page_p))  ==> is_valid_page[\old(l_to_p[lb][lp]) / N_PAGE][\old(l_to_p[lb][lp]) % N_PAGE] == false;
    ensures disk[ index_2_physical[\old(h_act_block_index_p)] ][\old(h_act_page_p)] == ghost_logical[lb][lp];
    ensures spare_area[ l_to_p[lb][lp] / N_PAGE ][ l_to_p[lb][lp] % N_PAGE ] == lb * N_PAGE + lp;
    ensures l_to_p[lb][lp] == index_2_physical[\old(h_act_block_index_p)] * N_PAGE + \old(h_act_page_p);
    ensures is_valid_page[ l_to_p[lb][lp] / N_PAGE ][ l_to_p[lb][lp] % N_PAGE ] == true;
    ensures in_P_range(h_act_block_index_p, h_act_page_p);
    ensures 0 <= l_to_p[lb][lp] < N_PHY_BLOCKS*N_PAGE;
    ensures (\old(h_act_page_p + 1 == N_PAGE)) ==> (h_act_page_p ==0);
    ensures ghost_logical[lb][lp] == d;
    ensures disk[(l_to_p[lb][lp] / N_PAGE)][(l_to_p[lb][lp] % N_PAGE)] == d;
    ensures 0 <= clean_counter <= N_PHY_BLOCKS ;
        
    behavior block_full:
        assumes h_act_page_p+1 == N_PAGE;
        ensures \forall integer i; (0 <= i < N_PHY_BLOCKS) && (i != index_2_physical[h_act_block_index_p]) ==> clean[i] == \old(clean[i]);
        ensures clean[index_2_physical[h_act_block_index_p]] == false;
    behavior block_not_full:
        assumes h_act_page_p+1 != N_PAGE;
        ensures \forall integer i; 0 <= i < N_PHY_BLOCKS ==> clean[i] == \old(clean[i]);
    complete behaviors;
    disjoint behaviors;
    


*/
void write_2_higher_number_list(int d, int lb, int lp){
    //invalidate old physical address
    //@ assert 0 <= l_to_p[lb][lp] < N_PHY_BLOCKS * N_PAGE || l_to_p[lb][lp] == -1;
    if(l_to_p[lb][lp] != -1){
        //@ assert   0 <= l_to_p[lb][lp] < N_PHY_BLOCKS * N_PAGE ;
        //clean previous physical address from the same logical address
        int old_addr = l_to_p[lb][lp];

        int opb = old_addr / N_PAGE; //turn page addressing to block id
        int opp = old_addr % N_PAGE; //turn page addressing to page offset
        is_valid_page[opb][opp] = false;
        
        
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
    
    //@ assert  (l_to_p[lb][lp] != -1) ==> is_valid_page[l_to_p[lb][lp] / N_PAGE][l_to_p[lb][lp] % N_PAGE] == true;

    //update active pointer value
   if(h_act_page_p + 1 == N_PAGE ){
        //page + 1 == block size
        //move the high pointer to the next clean block
        //firstly search a clean block from the head of the high number list
        h_act_page_p = 0;

        h_act_block_index_p = N_PHY_BLOCKS / 2;
        /*@
            loop assigns h_act_block_index_p;
            loop invariant (N_PHY_BLOCKS / 2) <= h_act_block_index_p <= N_PHY_BLOCKS;
            loop invariant \forall integer i; 0 <= i < N_PHY_BLOCKS ==> 0 <= index_2_physical[i] < N_PHY_BLOCKS;
        */
        while(h_act_block_index_p < N_PHY_BLOCKS && clean[index_2_physical[h_act_block_index_p]] == false ){
            h_act_block_index_p++;
        }
        
        //if no clean blocks in higher number list, then search clean block in lower number list
        if(h_act_block_index_p == N_PHY_BLOCKS){
            h_act_block_index_p = 0;
            /*@
                loop assigns h_act_block_index_p;
                loop invariant 0 <= h_act_block_index_p < N_PHY_BLOCKS / 2;
                loop invariant \forall integer i; 0 <= i < N_PHY_BLOCKS ==> 0 <= index_2_physical[i] < N_PHY_BLOCKS;

            */
            while (clean[index_2_physical[h_act_block_index_p]] == false && h_act_block_index_p < (N_PHY_BLOCKS / 2)){
                h_act_block_index_p++;
                if (h_act_block_index_p == N_PHY_BLOCKS/2) break;
            }
        }
        clean_counter -= 1;

        clean[index_2_physical[h_act_block_index_p]] = false;
    }else{
        //page + 1 < block size
        h_act_page_p +=1;
    }
    
    //count_clean_array(0,N_PHY_BLOCKS/2);
    
}
/*
* helper function of writting to lower num list
*    :param d: data
*    :param lb: logical block address
*    :param lp: logical page number
*    :return:
*/
/*@
    requires in_L_range(lb, lp);
    requires in_P_range(l_act_block_index_p, l_act_page_p);
    requires \valid(clean+(0.. N_PHY_BLOCKS-1));
    requires -2147483648 <= d <= 2147483647 ;
    requires 0 <= l_to_p[lb][lp] < N_PHY_BLOCKS * N_PAGE || l_to_p[lb][lp] == -1;
    requires ghost_logical[lb][lp] == d;
    requires 1 <= clean_counter <= N_PHY_BLOCKS ;
    requires 0 <= index_2_physical[l_act_block_index_p] < N_PHY_BLOCKS ;
    requires \forall integer i; 0 <= i < N_PHY_BLOCKS ==> 0 <= index_2_physical[i] < N_PHY_BLOCKS;

    assigns l_to_p[lb][lp] ;
    assigns is_valid_page[\old(l_to_p[lb][lp])/N_PAGE][\old(l_to_p[lb][lp]) % N_PAGE] ;
    assigns is_valid_page[ index_2_physical[\old(l_act_block_index_p)] ][\old(l_act_page_p)];
    assigns disk[ index_2_physical[\old(l_act_block_index_p)] ][\old(l_act_page_p)];
    assigns spare_area[ index_2_physical[\old(l_act_block_index_p)] ][\old(l_act_page_p)];
    assigns l_act_page_p ;
    assigns l_act_block_index_p ;
    assigns clean_counter;
    assigns clean[0..(N_PHY_BLOCKS - 1)];
    
    


    ensures ( \old(l_to_p[lb][lp]) != -1 ) && (\old(l_to_p[lb][lp]) / N_PAGE != \old(index_2_physical[\old(l_act_block_index_p)])) && (\old(l_to_p[lb][lp]) % N_PAGE != \old(l_act_page_p))  ==> is_valid_page[\old(l_to_p[lb][lp]) / N_PAGE][\old(l_to_p[lb][lp]) % N_PAGE] == false;
    ensures disk[ index_2_physical[\old(l_act_block_index_p)] ][\old(l_act_page_p)] == ghost_logical[lb][lp];
    ensures spare_area[ l_to_p[lb][lp] / N_PAGE ][ l_to_p[lb][lp] % N_PAGE ] == lb * N_PAGE + lp;
    ensures l_to_p[lb][lp] == index_2_physical[\old(l_act_block_index_p)] * N_PAGE + \old(l_act_page_p);
    ensures is_valid_page[ l_to_p[lb][lp] / N_PAGE ][ l_to_p[lb][lp] % N_PAGE ] == true;
    ensures in_P_range(l_act_block_index_p, l_act_page_p);
    ensures 0 <= l_to_p[lb][lp] < N_PHY_BLOCKS*N_PAGE;
    ensures (\old(l_act_page_p + 1 == N_PAGE)) ==> (l_act_page_p ==0);
    ensures ghost_logical[lb][lp] == d;
    ensures disk[(l_to_p[lb][lp] / N_PAGE)][(l_to_p[lb][lp] % N_PAGE)] == d;
    ensures 0 <= clean_counter <= N_PHY_BLOCKS ;
 
    behavior block_full:
        assumes l_act_page_p+1 == N_PAGE;
        ensures \forall integer i; (0 <= i < N_PHY_BLOCKS) && (i != index_2_physical[l_act_block_index_p]) ==> clean[i] == \old(clean[i]);
        ensures clean[index_2_physical[l_act_block_index_p]] == false;
    behavior block_not_full:
        assumes l_act_page_p+1 != N_PAGE;
        ensures \forall integer i; 0 <= i < N_PHY_BLOCKS ==> clean[i] == \old(clean[i]);
    complete behaviors;
    disjoint behaviors;

*/
void write_2_lower_number_list(int d, int lb, int lp){
    // invalidate  old physical address
    if(l_to_p[lb][lp] != -1){
        //clean previous physical address from the same logical address
        int old_addr = l_to_p[lb][lp];
        int opb = old_addr / N_PAGE; //turn page addressing to block id
        int opp = old_addr % N_PAGE; //turn page addressing to page offset
        is_valid_page[opb][opp] = false;
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
        /*@
            loop assigns l_act_block_index_p;
            loop invariant 0 <= l_act_block_index_p < N_PHY_BLOCKS;
            loop invariant \forall integer i; 0 <= i < N_PHY_BLOCKS ==> 0 <= index_2_physical[i] < N_PHY_BLOCKS;
        */
        while( l_act_block_index_p < N_PHY_BLOCKS-1 && clean[ index_2_physical[ l_act_block_index_p ]] == false ){
            l_act_block_index_p += 1;
        }
        //assert (0 <= l_act_block_index_p);
        //assert (l_act_block_index_p < N_PHY_BLOCKS);
        //@ assert 0 <= l_act_block_index_p < N_PHY_BLOCKS;
        //@ assert 0 <= index_2_physical[l_act_block_index_p] < N_PHY_BLOCKS ;

        clean_counter -= 1;

        clean[ index_2_physical[ l_act_block_index_p ] ] = false;
        
             
             
             
    }else{
        //page + 1 < block size
        l_act_page_p += 1;
    }
    //count_clean_array(0,N_PHY_BLOCKS/2);
}

/*
*perform garbage collection to ensure there is at least one clean block
*    :return:
*/
/*TODO
1.Never write to a non-clean page

2.max_wear() - min_wear() < tau

3.Informal: the disk behaves likes an array indexed with logical address
(Requires: forall lb1, lp1 . Ghost_disk[lb1][lp1] = Disk[l2p_b(lb1) ][ l2p_p(lp1)]
Ensures: forall lb1, lp1 . Ghost_disk[lb1][lp1] = Disk[l2p_b(lb1) ][ l2p_p(lp1)]
Ensures: Ghost_disk[lb][lp] =d
Ensures: forall lb1, lp1 .  lb1!=lb \/ lp1!=lp.  \uf0e8 Ghost_disk[lb1][lp1] = \old(Ghost_disk[lb1][lp1])
Ensures: Ghost_disk[lb][lp] =d = Disk[l2p_b(lb) ][ l2p_p(lp)])

*/
/*@
    requires 0 <= tau <= MAX_WEAR_CNT;
    requires unique(index_2_physical);
    requires \forall integer i; 0 <= i < N_PHY_BLOCKS ==> 0 <= index_2_physical[i] < N_PHY_BLOCKS;
    requires \forall integer i; 0 <= i < MAX_WEAR_CNT ==> erase_count_index[i] <= N_PHY_BLOCKS;
    requires 0 <= clean_counter < 2;
    requires clean_counter == count_clean(N_PHY_BLOCKS);
    requires clean_counter < N_PHY_BLOCKS - 2 ==>
        \exists integer i; 0 <= i < N_PHY_BLOCKS && i!=h_act_block_index_p && i!=l_act_block_index_p && clean[index_2_physical[i]]!=true;
    
    requires \forall integer i,j; 0 <= i < N_LOG_BLOCKS && 0 <= j < N_PAGE ==> 
        ghost_logical[i][j] == disk[(l_to_p[i][j] / N_PAGE)][(l_to_p[i][j] % N_PAGE)];


    assigns clean_counter;
    assigns h_act_block_index_p, l_act_block_index_p;
    assigns h_act_page_p, l_act_page_p ;
    assigns clean[0..(N_PHY_BLOCKS - 1)];
    assigns erase_count_index[0..(MAX_WEAR_CNT-1)];
    assigns index_2_physical[0..(N_PHY_BLOCKS-1)];
    assigns l_to_p[0..(N_LOG_BLOCKS - 1)][0..(N_PAGE)] ;  
    assigns clean[0..(N_PHY_BLOCKS - 1)];
    assigns spare_area[0..(N_PHY_BLOCKS - 1)][0..(N_PAGE-1)];
    assigns disk[0..(N_PHY_BLOCKS - 1)][0..(N_PAGE-1)];
    assigns is_valid_page[0..(N_PHY_BLOCKS - 1)][0..(N_PAGE-1)];

    ensures unique(index_2_physical);
    ensures 0 <= tau <= MAX_WEAR_CNT;
    ensures \forall integer i; 0 <= i < N_PHY_BLOCKS ==> 0 <= index_2_physical[i] < N_PHY_BLOCKS;
    ensures \forall integer i; 0 <= i < MAX_WEAR_CNT ==> erase_count_index[i] <= N_PHY_BLOCKS;
    ensures 2 <= clean_counter <= N_PHY_BLOCKS - 2;
    ensures clean_counter == count_clean(N_PHY_BLOCKS);
    ensures clean_counter < N_PHY_BLOCKS - 2 ==>
        \exists integer i; 0 <= i < N_PHY_BLOCKS && i!=h_act_block_index_p && i!=l_act_block_index_p && clean[index_2_physical[i]]!=true;

    ensures \forall integer i,j; 0 <= i < N_LOG_BLOCKS && 0 <= j < N_PAGE ==>
        ghost_logical[i][j] == disk[(l_to_p[i][j] / N_PAGE)][(l_to_p[i][j] % N_PAGE)];
*/
void gc(void){
    /*@
    loop invariant 0 <= tau <= MAX_WEAR_CNT;
    loop invariant unique(index_2_physical);
    loop invariant \forall integer i; 0 <= i < N_PHY_BLOCKS ==> 0 <= index_2_physical[i] < N_PHY_BLOCKS;
    loop invariant \forall integer i; 0 <= i < MAX_WEAR_CNT ==> erase_count_index[i] <= N_PHY_BLOCKS;
    loop invariant clean_counter == count_clean(N_PHY_BLOCKS);
    loop invariant 1 <= clean_counter <= N_PHY_BLOCKS - 2;
    loop invariant clean_counter < N_PHY_BLOCKS - 2 ==>
            \exists integer i; 0 <= i < N_PHY_BLOCKS && i!=h_act_block_index_p && i!=l_act_block_index_p && clean[index_2_physical[i]]!=true;
    
    loop assigns clean_counter;
    loop assigns clean[0..(N_PHY_BLOCKS - 1)];
    loop assigns h_act_block_index_p, l_act_block_index_p;
    loop assigns h_act_page_p, l_act_page_p ;
    loop assigns erase_count_index[0..(MAX_WEAR_CNT-1)];
    loop assigns index_2_physical[0..(N_PHY_BLOCKS-1)];
    loop assigns l_to_p[0..(N_LOG_BLOCKS - 1)][0..(N_PAGE)] ;  
    loop assigns clean[0..(N_PHY_BLOCKS - 1)];
    loop assigns spare_area[0..(N_PHY_BLOCKS - 1)][0..(N_PAGE-1)];
    loop assigns disk[0..(N_PHY_BLOCKS - 1)][0..(N_PAGE-1)];
    loop assigns is_valid_page[0..(N_PHY_BLOCKS - 1)][0..(N_PAGE-1)];
    */
    while(clean_counter < 2){
        int idx = get_most_clean_efficient_block_idx();
        if( min_wear() + tau <= get_erase_count_by_idx(idx) ){
       	    data_migration();
        }
        erase_block_data(idx);
        // assert clean_counter == \at(clean_counter, LoopCurrent) + 1;
    }
}
    /*
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
    }*/


/*
*perform data migration when victim block is in Maxwear
*/
/*@
    requires \forall integer i; 0 <= i < N_PHY_BLOCKS ==> 0 <= index_2_physical[i] < N_PHY_BLOCKS;
    requires 0 <= clean_counter < N_PHY_BLOCKS;
    requires 0 <= clean_counter < N_PHY_BLOCKS;
    requires \forall integer i; 0 <= i < MAX_WEAR_CNT ==> erase_count_index[i] <= N_PHY_BLOCKS;

    requires \forall integer i,j; 0 <= i < N_LOG_BLOCKS && 0 <= j < N_PAGE ==>
        ghost_logical[i][j] == disk[(l_to_p[i][j] / N_PAGE)][(l_to_p[i][j] % N_PAGE)];

    assigns clean_counter;
    assigns clean[0..(N_PHY_BLOCKS - 1)];
    assigns h_act_block_index_p, l_act_block_index_p;
    assigns erase_count_index[0..(MAX_WEAR_CNT-1)];
    assigns index_2_physical[0..(N_PHY_BLOCKS-1)];
    
    assigns l_to_p[0..(N_LOG_BLOCKS - 1)][0..(N_PAGE)] ;  
    assigns h_act_page_p ;
    assigns l_act_page_p ;
    assigns clean[0..(N_PHY_BLOCKS - 1)];

    assigns spare_area[0..(N_PHY_BLOCKS - 1)][0..(N_PAGE-1)];
    assigns disk[0..(N_PHY_BLOCKS - 1)][0..(N_PAGE-1)];
    assigns is_valid_page[0..(N_PHY_BLOCKS - 1)][0..(N_PAGE-1)]; 

    ensures \forall integer i,j; 0 <= i < N_LOG_BLOCKS && 0 <= j < N_PAGE ==>
        ghost_logical[i][j] == disk[(l_to_p[i][j] / N_PAGE)][(l_to_p[i][j] % N_PAGE)];
    */
void data_migration(void){
    // move all the block in min_wear
    int idx;
    if(min_wear() == 0){
        idx = 0;
    }else{
        idx = erase_count_index[min_wear() - 1]; // set index to the front of erase count i
    }
    int end_idx = erase_count_index[ min_wear() ];
/*@
    loop assigns clean_counter;
    loop assigns clean[0..(N_PHY_BLOCKS - 1)];
    loop assigns h_act_block_index_p, l_act_block_index_p;
    loop assigns erase_count_index[0..(MAX_WEAR_CNT-1)];
    loop assigns index_2_physical[0..(N_PHY_BLOCKS-1)];
    
    loop assigns l_to_p[0..(N_LOG_BLOCKS - 1)][0..(N_PAGE)] ;  
    loop assigns h_act_page_p ;
    loop assigns l_act_page_p ;
    loop assigns clean[0..(N_PHY_BLOCKS - 1)];

    loop assigns spare_area[0..(N_PHY_BLOCKS - 1)][0..(N_PAGE-1)];
    loop assigns disk[0..(N_PHY_BLOCKS - 1)][0..(N_PAGE-1)];
    loop assigns is_valid_page[0..(N_PHY_BLOCKS - 1)][0..(N_PAGE-1)];
    loop assigns idx;
    */
    while(idx < end_idx){    
        erase_block_data(idx);
        idx +=1;
    }
}

/*
* get the erase count of min wear
*   :return: min_wear value
*/
/*@
    requires \forall integer i,j; 0 <= i < N_LOG_BLOCKS && 0 <= j < N_PAGE ==>
        ghost_logical[i][j] == disk[(l_to_p[i][j] / N_PAGE)][(l_to_p[i][j] % N_PAGE)];

    assigns \nothing;
    ensures -1 <= \result <=  MAX_WEAR_CNT;
    ensures 0 <= \result < MAX_WEAR_CNT ==>
            erase_count_index[\result] != 0 &&
            \forall integer i; 0 <= i < \result ==> erase_count_index[i] == 0;
    ensures \result == -1 ==>
            \forall integer i; 0 <= i < MAX_WEAR_CNT ==> erase_count_index[i] == 0;

    ensures \forall integer i,j; 0 <= i < N_LOG_BLOCKS && 0 <= j < N_PAGE ==>
        ghost_logical[i][j] == disk[(l_to_p[i][j] / N_PAGE)][(l_to_p[i][j] % N_PAGE)];
 */
int min_wear(void){
    /*@ loop invariant 0 <= i <= MAX_WEAR_CNT;
    loop invariant \forall integer j; 0 <= j < i ==> erase_count_index[j] == 0;
        loop assigns i;
        loop variant MAX_WEAR_CNT - i;
    */
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
/*@
    requires \forall integer i,j; 0 <= i < N_LOG_BLOCKS && 0 <= j < N_PAGE ==>
        ghost_logical[i][j] == disk[(l_to_p[i][j] / N_PAGE)][(l_to_p[i][j] % N_PAGE)];

    assigns \nothing;
    ensures -1 <= \result <=  MAX_WEAR_CNT;

    ensures \forall integer i,j; 0 <= i < N_LOG_BLOCKS && 0 <= j < N_PAGE ==>
        ghost_logical[i][j] == disk[(l_to_p[i][j] / N_PAGE)][(l_to_p[i][j] % N_PAGE)];
 */
int max_wear(void){
    /*@ loop invariant 0 <= i <= MAX_WEAR_CNT;
        loop assigns i;
        loop variant MAX_WEAR_CNT-i;
    */
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
/*@ requires 0 <= idx < N_PHY_BLOCKS;
    requires \forall integer i; 0 <= i < MAX_WEAR_CNT ==> erase_count_index[i] <= N_PHY_BLOCKS;
    
    assigns \nothing;
    behavior not_reach_max_wear:
      assumes \exists integer i; 0 <= i < MAX_WEAR_CNT && erase_count_index[i] > idx;
      ensures 0 <= \result < MAX_WEAR_CNT;
      ensures erase_count_index[\result] > 0;
      
    behavior reach_max_wear:
      assumes \forall integer i; 0 <= i < MAX_WEAR_CNT ==> erase_count_index[i] <= idx;
      ensures \result == MAX_WEAR_CNT;

    complete behaviors;
    disjoint behaviors;
 */
int get_erase_count_by_idx(int idx){

    /*@ loop invariant 0 <= cur <=  MAX_WEAR_CNT;
        loop invariant \forall integer i; 0<=i<cur ==> erase_count_index[i] <= idx;
        loop assigns cur;
        loop variant MAX_WEAR_CNT-cur;
    */
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
/* requires 0 <= tau <= MAX_WEAR_CNT;
    requires 0 <= start_idx <  N_PHY_BLOCKS;
    requires 0 <= end_idx <=  N_PHY_BLOCKS;
    ensures 0 <= \result <  N_PHY_BLOCKS;
    assigns \nothing;

int find_vb(int start_idx, int end_idx){
    int idx = start_idx;
    int vic_idx = idx;
    int n_of_max_invalid_or_clean_page = 0;
    
     loop invariant start_idx <= idx <  N_PHY_BLOCKS;
        loop invariant start_idx <= vic_idx <  N_PHY_BLOCKS;
        loop assigns idx, vic_idx;
        loop variant end_idx-idx;
    
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

         loop invariant 0 <= pp <= N_PAGE;
            loop assigns n_of_invalid_or_clean_page, pp;
            loop variant N_PAGE-pp;
        
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
*/

/*
* this is similiar with _find_vb
* but it doesn't ignore blocks in Maxwear
*   :return: most_clean_efficient_idx
*/
/*@ requires \forall integer i; 0 <= i < N_PHY_BLOCKS ==> 0 <= index_2_physical[i] < N_PHY_BLOCKS;
    requires unique(index_2_physical);
    requires clean_counter == count_clean(N_PHY_BLOCKS);
    requires 0 <= clean_counter < N_PHY_BLOCKS - 2;
    requires 0 <= clean_counter < N_PHY_BLOCKS - 2 ==>
        \exists integer i; 0 <= i < N_PHY_BLOCKS && i!=h_act_block_index_p && i!=l_act_block_index_p && clean[index_2_physical[i]]!=true;
    
    requires \forall integer i,j; 0 <= i < N_LOG_BLOCKS && 0 <= j < N_PAGE ==>
        ghost_logical[i][j] == disk[(l_to_p[i][j] / N_PAGE)][(l_to_p[i][j] % N_PAGE)];

    assigns \nothing;
    
    ensures 0 <= \result <  N_PHY_BLOCKS;
    ensures \result != h_act_block_index_p && \result != l_act_block_index_p;
    ensures clean[index_2_physical[\result]] == false;
    ensures \forall integer i; 0<=i<N_PHY_BLOCKS && i!=h_act_block_index_p && i!=l_act_block_index_p && clean[index_2_physical[i]]!=true
        ==> count_efficiency(index_2_physical[\result], N_PAGE) >= count_efficiency(index_2_physical[i], N_PAGE);
    
    ensures \forall integer i,j; 0 <= i < N_LOG_BLOCKS && 0 <= j < N_PAGE ==>
        ghost_logical[i][j] == disk[(l_to_p[i][j] / N_PAGE)][(l_to_p[i][j] % N_PAGE)];
*/

int get_most_clean_efficient_block_idx(void){
    int most_efficient_idx = 0;
    int n_of_max_invalid_or_clean_page = 0;
    /*@ ghost bool start = false; */

    /*@ loop invariant 0 <= idx <= N_PHY_BLOCKS;
        loop invariant 0 <= most_efficient_idx < N_PHY_BLOCKS;
        loop invariant unique(index_2_physical);
        loop invariant \forall integer i; 0 <= i < N_PHY_BLOCKS ==> 0 <= index_2_physical[i] < N_PHY_BLOCKS;
        loop invariant 0 <= n_of_max_invalid_or_clean_page <= N_PAGE;
        
        loop invariant !start ==> most_efficient_idx == n_of_max_invalid_or_clean_page == 0;
        loop invariant !start ==> \forall integer i; 0<=i<idx ==> i==h_act_block_index_p || i==l_act_block_index_p || clean[index_2_physical[i]]==true;
        loop invariant start ==> n_of_max_invalid_or_clean_page == count_efficiency(index_2_physical[most_efficient_idx], N_PAGE);
        loop invariant start ==> most_efficient_idx!=h_act_block_index_p && most_efficient_idx!=l_act_block_index_p && clean[index_2_physical[most_efficient_idx]]!=true;
        
        loop invariant \forall integer i; 0<=i<idx && i!=h_act_block_index_p && i!=l_act_block_index_p && clean[index_2_physical[i]]!=true
            && most_efficient_idx!=h_act_block_index_p && most_efficient_idx!=l_act_block_index_p && clean[index_2_physical[most_efficient_idx]]!=true
            ==> count_efficiency(index_2_physical[most_efficient_idx], N_PAGE) >= count_efficiency(index_2_physical[i], N_PAGE);
        
        loop assigns  most_efficient_idx, n_of_max_invalid_or_clean_page, idx, start;
        loop variant N_PHY_BLOCKS - idx;
    */
    for(int idx = 0 ; idx < N_PHY_BLOCKS ; idx++){
        int pid = index_2_physical[idx];    // get physical block id

         //ignore the block indexed by either active pointer
        if (idx == h_act_block_index_p || idx == l_act_block_index_p){
            continue;
        }
        //ignore the block with all clean pages
        // this implementation is different from pseudo code
        if(clean[pid] == true){
            continue;
        }

        int n_of_invalid_or_clean_page = 0;
        /*@ loop invariant 0 <= pp <= N_PAGE;
            loop invariant 0 <= n_of_invalid_or_clean_page <= pp;
            loop invariant n_of_invalid_or_clean_page == count_efficiency(pid, pp);
            loop assigns n_of_invalid_or_clean_page, pp;
            loop variant N_PAGE - pp;
        */
        for(int pp = 0 ; pp < N_PAGE ; pp++){
            if(is_valid_page[pid][pp] == false){
                n_of_invalid_or_clean_page +=1;
            }
        }
                
        if(n_of_invalid_or_clean_page >= n_of_max_invalid_or_clean_page){
            most_efficient_idx = idx;
            n_of_max_invalid_or_clean_page = n_of_invalid_or_clean_page;
        }
        /*@ ghost start = true; */
    }
    return most_efficient_idx;
}

/*
* move valid page and erase this block; then increase erase cnt
*   :param idx: index in the index_2_physical
*   :return:
*/
/*@ requires 0 <= idx < N_PHY_BLOCKS;
    requires in_P_range(h_act_block_index_p, h_act_page_p);
    requires in_P_range(l_act_block_index_p, l_act_page_p);
    requires \forall integer i; 0 <= i < N_PHY_BLOCKS ==> 0 <= index_2_physical[i] < N_PHY_BLOCKS;
    requires 1 <= clean_counter < N_PHY_BLOCKS - 2;
    requires clean_counter == count_clean(N_PHY_BLOCKS);
    requires \exists integer i; 0 <= i < MAX_WEAR_CNT && erase_count_index[i] > idx;
    requires \forall integer i; 0 <= i < MAX_WEAR_CNT ==> erase_count_index[i] <= N_PHY_BLOCKS;
    requires in_P_range(h_act_block_index_p, h_act_page_p);
    requires in_P_range(l_act_block_index_p, l_act_page_p);
    requires 0 <= index_2_physical[h_act_block_index_p] < N_PHY_BLOCKS ;
    requires 0 <= l_array_counter < N_PHY_BLOCKS/2;
    requires idx != h_act_block_index_p && idx != l_act_block_index_p;
    requires clean[index_2_physical[idx]] == false;
    requires 0 <= tau <= MAX_WEAR_CNT;
    requires unique(index_2_physical);
    requires clean_counter < N_PHY_BLOCKS - 2 ==>
        \exists integer i; 0 <= i < N_PHY_BLOCKS && i!=h_act_block_index_p && i!=l_act_block_index_p && clean[index_2_physical[i]]!=true;

    requires \forall integer j; 0 <= j < N_PAGE && is_valid_page[index_2_physical[idx]][j] ==>
        ghost_logical[(spare_area[index_2_physical[idx]][j] / N_PAGE)][(spare_area[index_2_physical[idx]][j] % N_PAGE)] == 
            disk[l_to_p[(spare_area[index_2_physical[idx]][j] / N_PAGE)][(spare_area[index_2_physical[idx]][j] % N_PAGE)] / N_PAGE][l_to_p[(spare_area[index_2_physical[idx]][j] / N_PAGE)][(spare_area[index_2_physical[idx]][j] % N_PAGE)] % N_PAGE];

    assigns clean_counter;
    assigns h_act_block_index_p, l_act_block_index_p;
    assigns h_act_page_p, l_act_page_p ;
    assigns erase_count_index[0..(MAX_WEAR_CNT-1)];
    assigns index_2_physical[0..(N_PHY_BLOCKS-1)];
    assigns l_to_p[0..(N_LOG_BLOCKS - 1)][0..(N_PAGE - 1)] ;  
    assigns clean[0..(N_PHY_BLOCKS - 1)];
    assigns spare_area[0..(N_PHY_BLOCKS - 1)][0..(N_PAGE - 1)];
    assigns disk[0..(N_PHY_BLOCKS - 1)][0..(N_PAGE - 1)];
    assigns is_valid_page[0..(N_PHY_BLOCKS - 1)][0..(N_PAGE - 1)];

    ensures 0 <= tau <= MAX_WEAR_CNT;
    ensures unique(index_2_physical);
    ensures \forall integer i; 0 <= i < N_PHY_BLOCKS ==> 0 <= index_2_physical[i] < N_PHY_BLOCKS;
    ensures \forall integer i; 0 <= i < MAX_WEAR_CNT ==> erase_count_index[i] <= N_PHY_BLOCKS;
    ensures \forall integer i; 0 <= i < N_PAGE ==> is_valid_page[\old(index_2_physical[idx])][i] == false;
    ensures clean_counter == count_clean(N_PHY_BLOCKS);
    ensures 0 <= clean_counter <= N_PHY_BLOCKS - 2;
    ensures clean_counter < N_PHY_BLOCKS - 2 ==>
        \exists integer i; 0 <= i < N_PHY_BLOCKS && i!=h_act_block_index_p && i!=l_act_block_index_p && clean[index_2_physical[i]]!=true;  
    ensures clean[\old(index_2_physical[idx])] == true;
    ensures clean_counter == \old(clean_counter) + 1;

    ensures \forall integer j; 0 <= j < N_PAGE && is_valid_page[index_2_physical[idx]][j] ==>
        ghost_logical[(spare_area[index_2_physical[idx]][j] / N_PAGE)][(spare_area[index_2_physical[idx]][j] % N_PAGE)] == 
            disk[l_to_p[(spare_area[index_2_physical[idx]][j] / N_PAGE)][(spare_area[index_2_physical[idx]][j] % N_PAGE)] / N_PAGE][l_to_p[(spare_area[index_2_physical[idx]][j] / N_PAGE)][(spare_area[index_2_physical[idx]][j] % N_PAGE)] % N_PAGE];
    
 */
void erase_block_data(int idx){
    int pb = index_2_physical[idx]; //get physical block
    int pp = 0; //get physical page
    //copy valid page to another space and set the page to clean
    L:
    /*@ loop invariant 0 <= pp <= N_PAGE;
        loop invariant 0 <= pb <= N_PHY_BLOCKS;
        loop invariant 0 <= clean_counter < N_PHY_BLOCKS;
        loop invariant \forall integer i; 0 <= i < N_PHY_BLOCKS ==> index_2_physical[i] == \at(index_2_physical[i], L);
        loop invariant \forall integer i; 0 <= i < pp ==> is_valid_page[pb][i] == false;
        loop invariant in_P_range(h_act_block_index_p, h_act_page_p);
        loop invariant in_P_range(l_act_block_index_p, l_act_page_p);
        loop invariant \forall integer i; 0 <= i < N_PHY_BLOCKS ==> 0 <= index_2_physical[i] < N_PHY_BLOCKS;
        loop assigns pp; 
        loop assigns clean_counter;
        loop assigns h_act_page_p, l_act_page_p ;
        loop assigns h_act_block_index_p, l_act_block_index_p ;  
        loop assigns clean[0..(N_PHY_BLOCKS - 1)];
        loop assigns l_to_p[0..(N_LOG_BLOCKS - 1)][0..(N_PAGE - 1)] ;
        loop assigns spare_area[0..(N_PHY_BLOCKS - 1)][0..(N_PAGE - 1)];
        loop assigns disk[0..(N_PHY_BLOCKS - 1)][0..(N_PAGE - 1)];
        loop assigns is_valid_page[0..(N_PHY_BLOCKS - 1)][0..(N_PAGE - 1)];
        

        loop variant N_PAGE - pp;
     */
    while(pp != N_PAGE){
        if(is_valid_page[pb][pp]){
            int la = _read_spare_area(pb, pp); //get logical addr
            int lb = la / N_PAGE; //get logical block id
            int lp = la % N_PAGE;   //get logical page offset
            write_helper(_r(pb,pp), lb, lp);
        }
        is_valid_page[pb][pp] = false;
        pp++;
    }
    
    //erase the block by disk erase API
    _erase_block(pb);
    //update block clean status
    clean[pb] = true;

    //update clean counter
    clean_counter += 1;

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

/*@
    requires 0 <= idx < N_PHY_BLOCKS ;
    requires unique(index_2_physical);
    requires \exists integer i; 0 <= i < MAX_WEAR_CNT && erase_count_index[i] > idx;
    requires \forall integer i; 0 <= i < MAX_WEAR_CNT ==> erase_count_index[i] <= N_PHY_BLOCKS;
    requires \forall integer i; 0 <= i < N_PHY_BLOCKS ==> 0 <= index_2_physical[i] < N_PHY_BLOCKS;
    requires 2 <= clean_counter <= N_PHY_BLOCKS - 2;
    requires clean_counter == count_clean(N_PHY_BLOCKS);
    requires clean_counter < N_PHY_BLOCKS - 2 ==>
        \exists integer i; 0 <= i < N_PHY_BLOCKS && i!=h_act_block_index_p && i!=l_act_block_index_p && clean[index_2_physical[i]]!=true;
    
    requires \forall integer j; 0 <= j < N_PAGE && is_valid_page[index_2_physical[idx]][j] ==>
        ghost_logical[(spare_area[index_2_physical[idx]][j] / N_PAGE)][(spare_area[index_2_physical[idx]][j] % N_PAGE)] == 
            disk[l_to_p[(spare_area[index_2_physical[idx]][j] / N_PAGE)][(spare_area[index_2_physical[idx]][j] % N_PAGE)] / N_PAGE][l_to_p[(spare_area[index_2_physical[idx]][j] / N_PAGE)][(spare_area[index_2_physical[idx]][j] % N_PAGE)] % N_PAGE];

    assigns h_act_block_index_p, l_act_block_index_p;
    assigns clean_counter;
    assigns erase_count_index[0..(MAX_WEAR_CNT-1)];
    assigns index_2_physical[0..(N_PHY_BLOCKS-1)];

    
    ensures unique(index_2_physical);
    ensures \forall integer i; 0 <= i < N_PHY_BLOCKS ==> 0 <= index_2_physical[i] < N_PHY_BLOCKS;
    ensures \forall integer i; 0 <= i < MAX_WEAR_CNT ==> erase_count_index[i] <= N_PHY_BLOCKS;
    ensures 2 <= clean_counter <= N_PHY_BLOCKS - 2;
    ensures clean_counter == count_clean(N_PHY_BLOCKS);
    ensures clean_counter == \old(clean_counter);
    ensures \forall integer i; 0<=i<N_PHY_BLOCKS && i!=idx && index_2_physical[i]!=\old(index_2_physical[idx]) ==>
        index_2_physical[i] == \old(index_2_physical[i]);

    ensures \forall integer j; 0 <= j < N_PAGE && is_valid_page[index_2_physical[idx]][j] ==>
        ghost_logical[(spare_area[index_2_physical[idx]][j] / N_PAGE)][(spare_area[index_2_physical[idx]][j] % N_PAGE)] == 
            disk[l_to_p[(spare_area[index_2_physical[idx]][j] / N_PAGE)][(spare_area[index_2_physical[idx]][j] % N_PAGE)] / N_PAGE][l_to_p[(spare_area[index_2_physical[idx]][j] / N_PAGE)][(spare_area[index_2_physical[idx]][j] % N_PAGE)] % N_PAGE];
 */
void increase_erase_count(int idx){
    //swap the index_2_physical[idx] with the element which has teh same erase count
    int erase_count = get_erase_count_by_idx(idx); //get the erase cnt of idx
    int last_block_idx = erase_count_index[erase_count] - 1;    //get the ending index which has the same erase cnt

    /*@ assert \forall integer i; 0 <= i < N_LOG_BLOCKS ==> 0 <= index_2_physical[i] < N_PHY_BLOCKS; */
    /*@ assert \forall integer i; 0 <= i < MAX_WEAR_CNT ==> erase_count_index[i] <= N_PHY_BLOCKS; */
    /*@ assert index_bound: last_block_idx < 150; */

    // let active block pointer stay with the same blockID
    if(last_block_idx == h_act_block_index_p){
        h_act_block_index_p = idx;
    }
    if(last_block_idx == l_act_block_index_p){
        l_act_block_index_p = idx;
    }
    /*@ assert \forall integer i; 0 <= i < N_LOG_BLOCKS ==> 0 <= index_2_physical[i] < N_PHY_BLOCKS; */

    /*
    //need to check if idx and last_block_idx are clean?
    // if one of them are not clean, then need to update clean counter during swap
    if(clean[index_2_physical[last_block_idx]] == false){
        if(idx < (N_PHY_BLOCKS/2) && last_block_idx >= (N_PHY_BLOCKS/2)){
            l_clean_counter -= 1;
            h_clean_counter += 1;
        }
    }
    */
    
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
/*@
    requires -2147483648 <= d <= 2147483647;
    requires in_P_range(pb, pg);
    assigns disk[pb][pg];
    ensures disk[pb][pg] == d;
    
*/
void _w(int d, int pb, int pg){
   disk[pb][pg] = d;
   
}

/*
*    API
*    read from physical block address and page number
*    :param pb: physical block address
*    :param pg: physical page number
*    :return: data in this page
*/
/*@
    requires in_P_range(pb, pg);
    assigns \nothing;
    ensures -2147483648 <= \result <= 2147483647;
*/
int _r(int pb, int pg){
   return disk[pb][pg];
}

/*
*    DISK API
*    read logical page info from the space area
*    :param pb: physical block address
*    :param pp: physical page address
*    :return logical address:
*/
/*@
    requires in_P_range(pb, pp);
    assigns  \nothing;
    ensures 0 <= \result < N_LOG_BLOCKS * N_PAGE;
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
/*@
    requires 0 <= pb < N_PHY_BLOCKS ;
    requires 0 <= pp < N_PAGE ;
    requires in_P_range(pb, pp);
    requires 0 <= la < N_LOG_BLOCKS * N_PAGE ;
    assigns  spare_area[pb][pp];
    ensures  spare_area[pb][pp] == la ;
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
/*@
    assigns  \nothing;
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
/*@
    requires 0 <=  chance_index_p < LRU_SIZE;
    requires 0 <= lb * N_PAGE + lp < N_PHY_BLOCKS * N_PAGE ;
    requires 0 <= lb < N_LOG_BLOCKS &&  0 <= lp < N_PAGE ;
    assigns chance_index_p ;
    assigns chance_arr[0..(LRU_SIZE-1)];
    assigns cache[0..(LRU_SIZE-1)];
     
     
*/

void update_lru(int lb, int lp){
    int la = lb * N_PAGE + lp;  //get locical address (page addressing)
    int exist = find_and_update(la);    //check whether la in cache or not
    if(exist != 1){
        replace_and_update(la);     //if la is not in cache, then update cache
    }
}

/*
*   check whether logical addr la in cache
*   :param la: logical address
*   :return: if la in cache, then return 1; else return 0
*/
/*@
    requires 0 <= la < N_PHY_BLOCKS * N_PAGE ;
    assigns chance_arr[0..(LRU_SIZE-1)];
*/
int find_and_update(int la){
    /*@
        loop invariant 0 <= i <= LRU_SIZE;
        loop assigns i;
        loop variant LRU_SIZE - i;
    */
    for(int i=0 ; i<LRU_SIZE ; i++){
        if(cache[i] == la){
            chance_arr[i] = true;
            return 1;
        }
    }
    return 0;
}

/*  find an entry of no chance, replace it with la, update chance_arr
*   :param la: logical address
*   :return:
*/
/*@ requires 0 <=  chance_index_p < LRU_SIZE;
    requires 0 <= la < N_PHY_BLOCKS * N_PAGE ;
    assigns chance_index_p ;
    assigns cache[0..(LRU_SIZE-1)];
    assigns chance_arr[0..(LRU_SIZE-1)];
 */
void replace_and_update(int la){
    /*@ loop assigns cache[0..(LRU_SIZE-1)],chance_index_p, chance_arr[0..(LRU_SIZE-1)];
        loop invariant 0 <= chance_index_p < LRU_SIZE;
      */
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
*   :return: if la is in cache, then return 1; else return 0
*/
/*@
    requires in_L_range(lb, lp);
    requires in_P_range(h_act_block_index_p, h_act_page_p);
    requires 0 <= l_to_p[lb][lp] < 150*100 || l_to_p[lb][lp] == -1;
    assigns \nothing;

    ensures in_P_range(h_act_block_index_p, h_act_page_p);
    ensures 0 <= l_to_p[lb][lp] < 150*100 || l_to_p[lb][lp] == -1;
     
*/
int isHotPage(int lb, int lp){
    int la = lb * N_PAGE + lp;  //get logical address (page addressing)
    // currently brute force, traverse cache once
    /*@ loop invariant 0 <= i <= LRU_SIZE;
        loop assigns i;
    */
    for(int i=0 ; i<LRU_SIZE ; i++){
        if(cache[i] == la){
            return 1;
        }
    }
    return 0;
}

int main(void){
    initialize();
    write(0,0,0);
   
}