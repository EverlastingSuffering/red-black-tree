#ifndef RB_TREE_H
#define RB_TREE_H

#include "heap.h"

//#define RB_REVERSE
#ifdef RB_REVERSE
#define rb_compare(a,b) (a > b)
#else
#define rb_compare(a,b) (a < b)
#endif

typedef enum rb_color
{
    RB_RED,
    RB_BLACK
} __RB_COLOR;

#define rb_tree_t(RB_TYPE,BUFFER_SIZE,BUFFER_TYPE)                                                                                                                      \
    struct                                                                                                                                                              \
    {                                                                                                                                                                   \
        BUFFER_TYPE size,root;                                                                                                                                          \
        BUFFER_TYPE free_nodes[BUFFER_SIZE+1];                                                                                                                          \
        struct                                                                                                                                                          \
        {                                                                                                                                                               \
            __RB_COLOR color;                                                                                                                                           \
            RB_TYPE key;                                                                                                                                                \
            BUFFER_TYPE left,right,parent;                                                                                                                              \
        } buffer[BUFFER_SIZE+1];                                                                                                                                        \
    }

#define __rb_nil 0

#define rb_empty(tree) !(tree)->size

#define rb_size(tree) (tree)->size

#define __rb_node_by_index(tree,ind) tree->buffer[ind]

#define __rb_root_node(tree) tree->buffer[tree->root]

#define __rb_parent(tree,node) __rb_node_by_index(tree,node).parent

#define __rb_is_right_child(tree,node) (node == __rb_node_by_index(tree,__rb_parent(tree,node)).right)

#define __rb_grandparent(tree,node) __rb_parent(tree,__rb_parent(tree,node))

#define __rb_uncle(tree,node) (__rb_is_right_child(tree,__rb_parent(tree,node)) ? __rb_node_by_index(tree,__rb_grandparent(tree,node)).left : __rb_node_by_index(tree,__rb_grandparent(tree,node)).right)

#define __rb_sibling(tree,node) (__rb_is_right_child(tree,node) ? __rb_node_by_index(tree,__rb_parent(tree,node)).left : __rb_node_by_index(tree,__rb_parent(tree,node)).right)

#define __rb_key(tree,node) tree->buffer[node].key

#define __rb_color(tree,ind) __rb_node_by_index(tree,ind).color

#define __rb_add_root(tree,_key)                                                                                                                                        \
        {                                                                                                                                                               \
            hp_pop(tree->free_nodes,tree->root);                                                                                                                        \
            __rb_root_node(tree).color = RB_BLACK;                                                                                                                      \
            __rb_root_node(tree).key = _key;                                                                                                                            \
            __rb_root_node(tree).left = __rb_root_node(tree).right = __rb_nil;                                                                                          \
            __rb_root_node(tree).parent = __rb_nil;                                                                                                                     \
        }

#define __rb_allocate_node(tree,_parent,ind,_key)                                                                                                                       \
        {                                                                                                                                                               \
            hp_pop(tree->free_nodes,ind)                                                                                                                                \
            __rb_node_by_index(tree,ind).color = RB_RED;                                                                                                                \
            __rb_node_by_index(tree,ind).key = _key;                                                                                                                    \
            __rb_node_by_index(tree,ind).left = __rb_node_by_index(tree,ind).right = __rb_nil;                                                                          \
            __rb_node_by_index(tree,ind).parent = _parent;                                                                                                              \
        }

#define __rb_left_rotate(tree,node)                                                                                                                                     \
        {                                                                                                                                                               \
            long __rblr_node = node;                                                                                                                                    \
            long __rblr_y = __rb_node_by_index(tree,__rblr_node).right;                                                                                                 \
            __rb_node_by_index(tree,__rblr_node).right = __rb_node_by_index(tree,__rblr_y).left;                                                                        \
            if(__rb_node_by_index(tree,__rblr_y).left != __rb_nil)                                                                                                      \
                __rb_parent(tree,__rb_node_by_index(tree,__rblr_y).left) = __rblr_node;                                                                                 \
            __rb_parent(tree,__rblr_y) = __rb_parent(tree,__rblr_node);                                                                                                 \
            if(__rb_parent(tree,__rblr_node) == __rb_nil)                                                                                                               \
                tree->root = __rblr_y;                                                                                                                                  \
            else if(__rb_is_right_child(tree,__rblr_node))                                                                                                              \
                __rb_node_by_index(tree,__rb_parent(tree,__rblr_node)).right = __rblr_y;                                                                                \
            else                                                                                                                                                        \
                __rb_node_by_index(tree,__rb_parent(tree,__rblr_node)).left = __rblr_y;                                                                                 \
            __rb_node_by_index(tree,__rblr_y).left = __rblr_node;                                                                                                       \
            __rb_parent(tree,__rblr_node) = __rblr_y;                                                                                                                   \
        }

#define __rb_right_rotate(tree,node)                                                                                                                                    \
        {                                                                                                                                                               \
            long __rbrr_node = node;                                                                                                                                    \
            long __rbrr_y = __rb_node_by_index(tree,__rbrr_node).left;                                                                                                  \
            __rb_node_by_index(tree,__rbrr_node).left = __rb_node_by_index(tree,__rbrr_y).right;                                                                        \
            if(__rb_node_by_index(tree,__rbrr_y).right != __rb_nil)                                                                                                     \
                __rb_parent(tree,__rb_node_by_index(tree,__rbrr_y).right) = __rbrr_node;                                                                                \
            __rb_parent(tree,__rbrr_y) = __rb_parent(tree,__rbrr_node);                                                                                                 \
            if(__rb_parent(tree,__rbrr_node) == __rb_nil)                                                                                                               \
                tree->root = __rbrr_y;                                                                                                                                  \
            else if(__rb_is_right_child(tree,__rbrr_node))                                                                                                              \
                __rb_node_by_index(tree,__rb_parent(tree,__rbrr_node)).right = __rbrr_y;                                                                                \
            else                                                                                                                                                        \
                __rb_node_by_index(tree,__rb_parent(tree,__rbrr_node)).left = __rbrr_y;                                                                                 \
            __rb_node_by_index(tree,__rbrr_y).right = __rbrr_node;                                                                                                      \
            __rb_parent(tree,__rbrr_node) = __rbrr_y;                                                                                                                   \
        }

#define __rb_insert_fixup(tree,node)                                                                                                                                    \
        {                                                                                                                                                               \
            long __rbif_z = node;                                                                                                                                       \
            while(__rb_color(tree,__rb_parent(tree,__rbif_z)) == RB_RED)                                                                                                \
            {                                                                                                                                                           \
                long __rbif_y = __rb_uncle(tree,__rbif_z);                                                                                                              \
                if(!__rb_is_right_child(tree,__rb_parent(tree,__rbif_z)))                                                                                               \
                {                                                                                                                                                       \
                    if(__rb_color(tree,__rbif_y) == RB_RED)                                                                                                             \
                    {                                                                                                                                                   \
                        __rb_color(tree,__rb_grandparent(tree,__rbif_z)) = RB_RED;                                                                                      \
                        __rb_color(tree,__rb_parent(tree,__rbif_z)) = RB_BLACK;                                                                                         \
                        __rb_color(tree,__rbif_y) = RB_BLACK;                                                                                                           \
                        __rbif_z = __rb_grandparent(tree,__rbif_z);                                                                                                     \
                        continue;                                                                                                                                       \
                    }                                                                                                                                                   \
                    if(__rb_is_right_child(tree,__rbif_z))                                                                                                              \
                    {                                                                                                                                                   \
                        __rbif_z = __rb_parent(tree,__rbif_z);                                                                                                          \
                        __rb_left_rotate(tree,__rbif_z);                                                                                                                \
                    }                                                                                                                                                   \
                    __rb_color(tree,__rb_parent(tree,__rbif_z)) = RB_BLACK;                                                                                             \
                    __rb_color(tree,__rb_grandparent(tree,__rbif_z)) = RB_RED;                                                                                          \
                    __rb_right_rotate(tree,__rb_grandparent(tree,__rbif_z));                                                                                            \
                }                                                                                                                                                       \
                else                                                                                                                                                    \
                {                                                                                                                                                       \
                    if(__rb_color(tree,__rbif_y) == RB_RED)                                                                                                             \
                    {                                                                                                                                                   \
                        __rb_color(tree,__rb_grandparent(tree,__rbif_z)) = RB_RED;                                                                                      \
                        __rb_color(tree,__rb_parent(tree,__rbif_z)) = RB_BLACK;                                                                                         \
                        __rb_color(tree,__rbif_y) = RB_BLACK;                                                                                                           \
                        __rbif_z = __rb_grandparent(tree,__rbif_z);                                                                                                     \
                        continue;                                                                                                                                       \
                    }                                                                                                                                                   \
                    if(!__rb_is_right_child(tree,__rbif_z))                                                                                                             \
                    {                                                                                                                                                   \
                        __rbif_z = __rb_parent(tree,__rbif_z);                                                                                                          \
                        __rb_right_rotate(tree,__rbif_z);                                                                                                               \
                    }                                                                                                                                                   \
                    __rb_color(tree,__rb_parent(tree,__rbif_z)) = RB_BLACK;                                                                                             \
                    __rb_color(tree,__rb_grandparent(tree,__rbif_z)) = RB_RED;                                                                                          \
                    __rb_left_rotate(tree,__rb_grandparent(tree,__rbif_z));                                                                                             \
                }                                                                                                                                                       \
            }                                                                                                                                                           \
            __rb_color(tree,tree->root) = RB_BLACK;                                                                                                                     \
        }

#define __rb_transplant(tree,u,v)                                                                                                                                       \
        if(__rb_parent(tree,u) == __rb_nil)                                                                                                                             \
        {                                                                                                                                                               \
            tree->root = v;                                                                                                                                             \
        }                                                                                                                                                               \
        else if(__rb_is_right_child(tree,u))                                                                                                                            \
            __rb_node_by_index(tree,__rb_parent(tree,u)).right = v;                                                                                                     \
        else                                                                                                                                                            \
            __rb_node_by_index(tree,__rb_parent(tree,u)).left = v;                                                                                                      \
        __rb_parent(tree,v) = __rb_parent(tree,u);

#define __rb_mintree(tree,node,ret)                                                                                                                                     \
        ret = node;                                                                                                                                                     \
        while(__rb_node_by_index(tree,ret).left != __rb_nil && ret != __rb_nil)                                                                                         \
            ret = __rb_node_by_index(tree,ret).left;

#define rb_init(tree)                                                                                                                                                   \
        {                                                                                                                                                               \
            __rb_node_by_index((tree),__rb_nil).color = RB_BLACK;                                                                                                       \
            __rb_node_by_index((tree),__rb_nil).left =                                                                                                                  \
                                    __rb_node_by_index((tree),__rb_nil).right =                                                                                         \
                                    __rb_node_by_index((tree),__rb_nil).parent = __rb_nil;                                                                              \
            (tree)->size = 0;                                                                                                                                           \
            hp_init((tree)->free_nodes);                                                                                                                                \
            for(long i = 1; i < sizeof((tree)->free_nodes)/sizeof(((tree)->free_nodes[0])); ++i)                                                                        \
                hp_insert((tree)->free_nodes,i)                                                                                                                         \
        }

#define rb_find(tree,_key,ind)                                                                                                                                          \
        {                                                                                                                                                               \
            ind = (tree)->root;                                                                                                                                         \
            while(__rb_key((tree),ind) != _key && ind != __rb_nil)                                                                                                      \
                ind = rb_compare(__rb_key((tree),ind),_key) ? __rb_node_by_index((tree),ind).right :                                                                    \
                                                        __rb_node_by_index((tree),ind).left;                                                                            \
        }


#define rb_insert(tree,_key)                                                                                                                                            \
        {                                                                                                                                                               \
            if(rb_empty(tree))                                                                                                                                          \
                __rb_add_root((tree),_key)                                                                                                                              \
            else                                                                                                                                                        \
            {                                                                                                                                                           \
                long __rbi_current_node = __rb_nil;                                                                                                                     \
                long __rbi_next_node = (tree)->root;                                                                                                                    \
                while(__rbi_next_node != __rb_nil)                                                                                                                      \
                {                                                                                                                                                       \
                    __rbi_current_node = __rbi_next_node;                                                                                                               \
                    if(rb_compare(__rb_node_by_index((tree),__rbi_current_node).key,_key))                                                                              \
                        __rbi_next_node = __rb_node_by_index((tree),__rbi_current_node).right;                                                                          \
                    else                                                                                                                                                \
                        __rbi_next_node = __rb_node_by_index((tree),__rbi_current_node).left;                                                                           \
                }                                                                                                                                                       \
                __rb_allocate_node((tree),__rbi_current_node,__rbi_next_node,_key)                                                                                      \
                if(rb_compare(__rb_node_by_index((tree),__rbi_current_node).key,_key))                                                                                  \
                    __rb_node_by_index((tree),__rbi_current_node).right = __rbi_next_node;                                                                              \
                else                                                                                                                                                    \
                    __rb_node_by_index((tree),__rbi_current_node).left = __rbi_next_node;                                                                               \
                __rb_insert_fixup((tree),__rbi_next_node);                                                                                                              \
            }                                                                                                                                                           \
            (tree)->size++;                                                                                                                                             \
        }

#define __rb_delete_fixup(tree,node)                                                                                                                                    \
        {                                                                                                                                                               \
            while(node != tree->root && __rb_color(tree,node) == RB_BLACK)                                                                                              \
            {                                                                                                                                                           \
                if(__rb_is_right_child(tree,node))                                                                                                                      \
                {                                                                                                                                                       \
                    long __rbdf_w = __rb_node_by_index(tree,__rb_parent(tree,node)).left;                                                                               \
                    if(__rb_color(tree,__rbdf_w) == RB_RED)                                                                                                             \
                    {                                                                                                                                                   \
                        __rb_color(tree,__rbdf_w) = RB_BLACK;                                                                                                           \
                        __rb_color(tree,__rb_parent(tree,node)) = RB_RED;                                                                                               \
                        __rb_right_rotate(tree,__rb_parent(tree,node));                                                                                                 \
                        __rbdf_w = __rb_node_by_index(tree,__rb_parent(tree,node)).left;                                                                                \
                    }                                                                                                                                                   \
                    if(__rb_color(tree,__rb_node_by_index(tree,__rbdf_w).left) == RB_BLACK && __rb_color(tree,__rb_node_by_index(tree,__rbdf_w).right) == RB_BLACK)     \
                    {                                                                                                                                                   \
                        __rb_color(tree,__rbdf_w) = RB_RED;                                                                                                             \
                        node = __rb_parent(tree,node);                                                                                                                  \
                        continue;                                                                                                                                       \
                    }                                                                                                                                                   \
                    if(__rb_color(tree,__rb_node_by_index(tree,__rbdf_w).left) == RB_BLACK)                                                                             \
                    {                                                                                                                                                   \
                        __rb_color(tree,__rb_node_by_index(tree,__rbdf_w).right) = RB_BLACK;                                                                            \
                        __rb_color(tree,__rbdf_w) = RB_RED;                                                                                                             \
                        __rb_left_rotate(tree,__rbdf_w);                                                                                                                \
                        __rbdf_w = __rb_node_by_index(tree,__rb_parent(tree,node)).left;                                                                                \
                    }                                                                                                                                                   \
                    if(__rb_color(tree,__rb_node_by_index(tree,__rbdf_w).left) == RB_RED)                                                                               \
                    {                                                                                                                                                   \
                        __rb_color(tree,__rbdf_w) = __rb_color(tree,__rb_parent(tree,node));                                                                            \
                        __rb_color(tree,__rb_parent(tree,node)) = RB_BLACK;                                                                                             \
                        __rb_color(tree,__rb_node_by_index(tree,__rbdf_w).left) = RB_BLACK;                                                                             \
                        __rb_right_rotate(tree,__rb_parent(tree,node));                                                                                                 \
                        node = tree->root;                                                                                                                              \
                    }                                                                                                                                                   \
                }                                                                                                                                                       \
                else                                                                                                                                                    \
                {                                                                                                                                                       \
                    long __rbdf_w = __rb_node_by_index(tree,__rb_parent(tree,node)).right;                                                                              \
                    if(__rb_color(tree,__rbdf_w) == RB_RED)                                                                                                             \
                    {                                                                                                                                                   \
                        __rb_color(tree,__rbdf_w) = RB_BLACK;                                                                                                           \
                        __rb_color(tree,__rb_parent(tree,node)) = RB_RED;                                                                                               \
                        __rb_left_rotate(tree,__rb_parent(tree,node));                                                                                                  \
                        __rbdf_w = __rb_node_by_index(tree,__rb_parent(tree,node)).right;                                                                               \
                    }                                                                                                                                                   \
                    if(__rb_color(tree,__rb_node_by_index(tree,__rbdf_w).left) == RB_BLACK && __rb_color(tree,__rb_node_by_index(tree,__rbdf_w).right) == RB_BLACK)     \
                    {                                                                                                                                                   \
                        __rb_color(tree,__rbdf_w) = RB_RED;                                                                                                             \
                        node = __rb_parent(tree,node);                                                                                                                  \
                        continue;                                                                                                                                       \
                    }                                                                                                                                                   \
                    if(__rb_color(tree,__rb_node_by_index(tree,__rbdf_w).right) == RB_BLACK)                                                                            \
                    {                                                                                                                                                   \
                        __rb_color(tree,__rb_node_by_index(tree,__rbdf_w).left) = RB_BLACK;                                                                             \
                        __rb_color(tree,__rbdf_w) = RB_RED;                                                                                                             \
                        __rb_right_rotate(tree,__rbdf_w);                                                                                                               \
                        __rbdf_w = __rb_node_by_index(tree,__rb_parent(tree,node)).right;                                                                               \
                    }                                                                                                                                                   \
                    if(__rb_color(tree,__rb_node_by_index(tree,__rbdf_w).right) == RB_RED)                                                                              \
                    {                                                                                                                                                   \
                        __rb_color(tree,__rbdf_w) = __rb_color(tree,__rb_parent(tree,node));                                                                            \
                        __rb_color(tree,__rb_parent(tree,node)) = RB_BLACK;                                                                                             \
                        __rb_color(tree,__rb_node_by_index(tree,__rbdf_w).right) = RB_BLACK;                                                                            \
                        __rb_left_rotate(tree,__rb_parent(tree,node));                                                                                                  \
                        node = tree->root;                                                                                                                              \
                    }                                                                                                                                                   \
                }                                                                                                                                                       \
            }                                                                                                                                                           \
            __rb_color(tree,node) = RB_BLACK;                                                                                                                           \
        }

#define rb_erase(tree,ind)                                                                                                                                              \
        {                                                                                                                                                               \
            long __rbe_y = ind;                                                                                                                                         \
            __RB_COLOR y_orig_color = __rb_color((tree),__rbe_y);                                                                                                       \
            long __rbe_x;                                                                                                                                               \
            if(__rb_node_by_index((tree),ind).left == __rb_nil)                                                                                                         \
            {                                                                                                                                                           \
                __rbe_x = __rb_node_by_index((tree),ind).right;                                                                                                         \
                __rb_transplant((tree),ind,__rb_node_by_index((tree),ind).right)                                                                                        \
            }                                                                                                                                                           \
            else if(__rb_node_by_index((tree),ind).right == __rb_nil)                                                                                                   \
            {                                                                                                                                                           \
                __rbe_x = __rb_node_by_index((tree),ind).left;                                                                                                          \
                __rb_transplant((tree),ind,__rb_node_by_index((tree),ind).left)                                                                                         \
            }                                                                                                                                                           \
            else                                                                                                                                                        \
            {                                                                                                                                                           \
                __rb_mintree((tree),__rb_node_by_index((tree),ind).right,__rbe_y)                                                                                       \
                y_orig_color = __rb_color((tree),__rbe_y);                                                                                                              \
                __rbe_x = __rb_node_by_index((tree),__rbe_y).right;                                                                                                     \
                if(__rb_parent((tree),__rbe_y) != ind)                                                                                                                  \
                {                                                                                                                                                       \
                    __rb_transplant((tree),__rbe_y,__rb_node_by_index((tree),__rbe_y).right)                                                                            \
                    __rb_node_by_index((tree),__rbe_y).right = __rb_node_by_index((tree),ind).right;                                                                    \
                    __rb_parent((tree),__rb_node_by_index((tree),__rbe_y).right) = __rbe_y;                                                                             \
                }                                                                                                                                                       \
                else                                                                                                                                                    \
                    __rb_parent((tree),__rbe_x) = __rbe_y;                                                                                                              \
                __rb_transplant((tree),ind,__rbe_y)                                                                                                                     \
                __rb_node_by_index((tree),__rbe_y).left = __rb_node_by_index((tree),ind).left;                                                                          \
                __rb_parent((tree),__rb_node_by_index((tree),__rbe_y).left) = __rbe_y;                                                                                  \
                __rb_color((tree),__rbe_y) = __rb_color((tree),ind);                                                                                                    \
            }                                                                                                                                                           \
            if(y_orig_color == RB_BLACK)                                                                                                                                \
                __rb_delete_fixup((tree),__rbe_x);                                                                                                                      \
            (tree)->size--;                                                                                                                                             \
            hp_insert((tree)->free_nodes,ind);                                                                                                                          \
        }

#endif