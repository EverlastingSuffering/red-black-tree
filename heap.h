#ifndef __HEAP_H
#define __HEAP_H

// Define MIN_HEAP to compile min-heap and MAX_HEAP otherwise
#define MIN_HEAP
//#define MAX_HEAP

// Return codes
#define HP_SUCCESS 0
#define HP_HEAP_EMPTY 1
#define HP_INDEX_OUT_OF_RANGE 2
#define HP_INVALID_KEY 3

// Compare function
#ifdef MIN_HEAP
#define hp_compare(a,b) (a < b)
#else
#define hp_compare(a,b) (a > b)
#endif

#define hp_empty(heap) (heap[0] == 0)

#define hp_size(heap) heap[0]

#define hp_in_heap(heap,i) ((i <= hp_size(heap)) && (i > 0))

#define hp_left_child(i) (2*i)
#define hp_right_child(i) (2*i+1)
#define hp_parent(i) (i/2)
#define hp_root 1

#define hp_swap(heap,i,j)                                                                                               \
            heap[i] = heap[i] + heap[j];                                                                                \
            heap[j] = heap[i] - heap[j];                                                                                \
            heap[i] = heap[i] - heap[j];

#define hp_init(heap) heap[0] = 0;

// Restore heap properties of subtree with root 'i'.
#define hp_heapify(heap,ind)                                                                                            \
{                                                                                                                       \
    long __hph_i = ind;                                                                                                 \
    while(1)                                                                                                            \
    {                                                                                                                   \
        long __hph_largest = __hph_i;                                                                                   \
        if(hp_in_heap(heap,hp_left_child(__hph_i)) && hp_compare(heap[hp_left_child(__hph_i)],heap[__hph_largest]))     \
            __hph_largest = hp_left_child(__hph_i);                                                                     \
        if(hp_in_heap(heap,hp_right_child(__hph_i)) && hp_compare(heap[hp_right_child(__hph_i)],heap[__hph_largest]))   \
            __hph_largest = hp_right_child(__hph_i);                                                                    \
        if(__hph_largest != __hph_i)                                                                                    \
        {                                                                                                               \
            hp_swap(heap,__hph_largest,__hph_i)                                                                         \
            __hph_i = __hph_largest;                                                                                    \
        }                                                                                                               \
        else                                                                                                            \
            break;                                                                                                      \
    }                                                                                                                   \
}

// Increases (MAX_HEAP) or decreases (MIN_HEAP) value of i-th element.
#define hp_change_key(heap,ind,key)                                                                                     \
{                                                                                                                       \
    long __hpck_i = ind;                                                                                                \
    heap[__hpck_i] = key;                                                                                               \
    while(__hpck_i > hp_root && hp_compare(heap[__hpck_i],heap[hp_parent(__hpck_i)]))                                   \
    {                                                                                                                   \
        hp_swap(heap,__hpck_i,hp_parent(__hpck_i))                                                                      \
        __hpck_i = hp_parent(__hpck_i);                                                                                 \
    }                                                                                                                   \
}

// Inserts new element with value=key
#define hp_insert(heap,key)                                                                                             \
{                                                                                                                       \
    hp_size(heap)++;                                                                                                    \
    heap[hp_size(heap)] = key;                                                                                          \
    hp_change_key(heap,hp_size(heap),key);                                                                              \
}

// Removes max (MAX_HEAP) or min (MIN_HEAP) element from heap and puts it in 'out'
#define hp_pop(heap,out)                                                                                                \
{                                                                                                                       \
        out = heap[hp_root];                                                                                            \
        heap[hp_root] = heap[hp_size(heap)];                                                                            \
        hp_size(heap)--;                                                                                                \
        if(!hp_empty(heap))                                                                                             \
        {                                                                                                               \
            hp_heapify(heap,hp_root);                                                                                   \
        }                                                                                                               \
}

#define hp_erase(heap)                                                                                                  \
{                                                                                                                       \
        heap[hp_root] = heap[hp_size(heap)];                                                                            \
        hp_size(heap)--;                                                                                                \
        if(!hp_empty(heap))                                                                                             \
        {                                                                                                               \
            hp_heapify(heap,hp_root);                                                                                   \
        }                                                                                                               \
}

#endif