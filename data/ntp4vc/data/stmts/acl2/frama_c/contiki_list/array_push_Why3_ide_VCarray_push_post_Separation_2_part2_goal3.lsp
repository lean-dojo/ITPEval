;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/contiki_list/array_push_Why3_ide_VCarray_push_post_Separation_2_part2_goal3:
;; separation of two distinct entries after a null update to a havoced
;; pointer array during array push. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun apsg3-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun apsg3-address-base (address)
  (car address))

(defun apsg3-address-offset (address)
  (cdr address))

(defun apsg3-shift (address amount)
  (cons
   (apsg3-address-base address)
   (+ (apsg3-address-offset address) amount)))

;; These conservative symbols represent the universally arbitrary source
;; functions t_2, t_3, and t, and the fixed region and linked symbols.

(defstub apsg3-t2 (address) t)
(defstub apsg3-t3 (address) t)
(defstub apsg3-malloc (index) t)
(defstub apsg3-region (base) t)
(defstub apsg3-linked-op () t)

(defun-sk apsg3-pointer-functions-p ()
  (forall (address)
    (implies
     (apsg3-address-p address)
     (and
      (apsg3-address-p (apsg3-t2 address))
      (apsg3-address-p (apsg3-t3 address))))))

(defun-sk apsg3-malloc-function-p ()
  (forall (index)
    (implies
     (integerp index)
     (integerp (apsg3-malloc index)))))

(defun-sk apsg3-region-function-p ()
  (forall (base)
    (implies
     (integerp base)
     (integerp (apsg3-region base)))))

(defun apsg3-linked-p ()
  (if (apsg3-linked-op) t nil))

(defun apsg3-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun apsg3-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (apsg3-address-base left)
     (apsg3-address-base right)))
   (<=
    (+ (apsg3-address-offset right) right-length)
    (apsg3-address-offset left))
   (<=
    (+ (apsg3-address-offset left) left-length)
    (apsg3-address-offset right))))

(defun apsg3-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (apsg3-address-base address))
    (<= 0 (apsg3-address-offset address))
    (<=
     (+ (apsg3-address-offset address) length)
     (apsg3-malloc (apsg3-address-base address))))))

;; HAVOC-READ is the source memory-theory havoc operation, characterized by
;; its access equation.

(defun apsg3-havoc-read
    (havoc-start havoc-length address)
  (if
      (apsg3-separated-p address 1 havoc-start havoc-length)
      (apsg3-t3 address)
    (apsg3-t2 address)))

;; UPDATED-READ is the exact functional update of the second havoced memory
;; at the designated array slot with the null address.

(defun apsg3-updated-read
    (havoc-start havoc-length update-address address)
  (if (equal address update-address)
      (cons 0 0)
    (apsg3-havoc-read havoc-start havoc-length address)))

(defun apsg3-mptr-read
    (memory-kind havoc-start havoc-length address)
  (cond
   ((equal memory-kind :t3)
    (apsg3-t3 address))
   ((equal memory-kind :a5)
    (apsg3-havoc-read havoc-start havoc-length address))
   (t nil)))

;; This recursion is equivalent to the source inductive p_linked_n relation:
;; n = 0 is its bound constructor, while n > 0 is its cons constructor
;; followed by the unique recursive predecessor at n - 1.

(defun apsg3-p-linked-n-p
    (memory-kind havoc-start havoc-length
                 root array index n bound)
  (declare (xargs :measure (nfix n)))
  (and
   (member-eq memory-kind '(:t3 :a5))
   (apsg3-address-p root)
   (apsg3-address-p array)
   (integerp index)
   (integerp n)
   (apsg3-address-p bound)
   (if (equal n 0)
       (and
        (equal root bound)
        (<= 0 index)
        (<= index 2147483646))
     (and
      (< 0 n)
      (equal
       (apsg3-mptr-read
        memory-kind havoc-start havoc-length
        (apsg3-shift array index))
       root)
      (<= 0 index)
      (<= 0 (+ index n))
      (<= (+ index n) 2147483646)
      (apsg3-valid-rw-p root 4)
      (apsg3-p-linked-n-p
       memory-kind havoc-start havoc-length
       (apsg3-mptr-read
        memory-kind havoc-start havoc-length
        (apsg3-shift root 0))
       array
       (+ 1 index)
       (- n 1)
       bound)))))

(defun-sk apsg3-framed-p ()
  (forall (address)
    (implies
     (apsg3-address-p address)
     (<=
      (apsg3-region
       (apsg3-address-base (apsg3-t3 address)))
      0))))

(defun-sk apsg3-array-swipe-right-p
    (havoc-start havoc-length array down up)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= down index)
      (< index up))
     (equal
      (apsg3-t3 (apsg3-shift array (- index 1)))
      (apsg3-havoc-read
       havoc-start havoc-length
       (apsg3-shift array index))))))

;; The source p_unchanged uses the same malloc function and real-valued memory
;; on both sides. Unfolding load_s1_list and eqs1_list makes the real fields
;; equal once the selected addresses are equal; the next-pointer equality and
;; valid_rw implication below are precisely the remaining conjuncts.

(defun-sk apsg3-unchanged-p
    (havoc-start havoc-length array down up)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= down index)
      (< index up))
     (let*
         ((slot (apsg3-shift array index))
          (left-address
           (apsg3-havoc-read
            havoc-start havoc-length slot))
          (right-address (apsg3-t3 slot)))
       (and
        (equal left-address right-address)
        (equal
         (apsg3-t3 (apsg3-shift right-address 0))
         (apsg3-havoc-read
          havoc-start havoc-length
          (apsg3-shift left-address 0)))
        (implies
         (apsg3-valid-rw-p right-address 4)
         (apsg3-valid-rw-p left-address 4)))))))

(defun-sk apsg3-a1-separated-t3-range-p
    (a1 array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (apsg3-separated-p
      a1 1
      (apsg3-t3 (apsg3-shift array index))
      4))))

(defun-sk apsg3-t3-range-separated-from-array-p
    (array-base array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (apsg3-separated-p
      (apsg3-t3 (apsg3-shift array index))
      4 array-base 2147483646))))

(defun-sk apsg3-t3-range-addresses-distinct-p
    (array lower upper)
  (forall (left-index right-index)
    (implies
     (and
      (integerp left-index)
      (integerp right-index)
      (not (equal left-index right-index))
      (<= lower right-index)
      (<= lower left-index)
      (< right-index upper)
      (< left-index upper))
     (not
      (equal
       (apsg3-t3 (apsg3-shift array left-index))
       (apsg3-t3 (apsg3-shift array right-index)))))))

(defun-sk apsg3-t3-range-addresses-separated-p
    (array lower upper)
  (forall (left-index right-index)
    (implies
     (and
      (integerp left-index)
      (integerp right-index)
      (not (equal left-index right-index))
      (<= lower right-index)
      (<= lower left-index)
      (< right-index upper)
      (< left-index upper))
     (apsg3-separated-p
      (apsg3-t3 (apsg3-shift array left-index))
      4
      (apsg3-t3 (apsg3-shift array right-index))
      4))))

(defun-sk apsg3-a1-separated-a5-open-closed-range-p
    (a1 array lower upper havoc-start havoc-length)
  (forall (index)
    (implies
     (and
      (integerp index)
      (< lower index)
      (<= index upper))
     (apsg3-separated-p
      a1 1
      (apsg3-havoc-read
       havoc-start havoc-length
       (apsg3-shift array index))
      4))))

(defun-sk apsg3-a5-range-separated-from-array-p
    (array-base array lower upper havoc-start havoc-length)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (apsg3-separated-p
      (apsg3-havoc-read
       havoc-start havoc-length
       (apsg3-shift array index))
      4 array-base 2147483646))))

(defun-sk
    ntp4vc-array-push-post-separation-2-part2-goal3-statement ()
  (forall
   (i1 i2 a4 a1 i3 i5 i4 i a a3 a2)
   (implies
    (and
     (integerp i1)
     (integerp i2)
     (apsg3-address-p a4)
     (apsg3-address-p a1)
     (integerp i3)
     (integerp i5)
     (integerp i4)
     (integerp i)
     (apsg3-address-p a)
     (apsg3-address-p a3)
     (apsg3-address-p a2)
     (apsg3-pointer-functions-p)
     (apsg3-malloc-function-p)
     (apsg3-region-function-p))
    (let*
        ((x (+ i1 i2))
         (a5-havoc-start (apsg3-shift a4 (+ 1 i2)))
         (a5-havoc-length i1)
         (a6 (apsg3-t3 a1))
         (a7 (apsg3-shift a4 0))
         (x1 (+ 1 i3))
         (a8-havoc-start (apsg3-shift a4 x1))
         (a8-havoc-length i1)
         (a8-update-address (apsg3-shift a4 i3)))
      (implies
       (and
        (not (equal i1 0))
        (not (equal i5 i4))
        (equal (equal x i3) (equal i 0))
        (equal (< i3 x) (equal i 1))
        (equal
         (apsg3-havoc-read
          a5-havoc-start a5-havoc-length a1)
         a6)
        (<= i3 i2)
        (< i2 i4)
        (< i2 i5)
        (<= i2 i3)
        (<= i3 x)
        (<= i4 x)
        (<= i5 x)
        (<= (apsg3-region (apsg3-address-base a)) 0)
        (<= (apsg3-region (apsg3-address-base a1)) 0)
        (<= (apsg3-region (apsg3-address-base a3)) 0)
        (<= (apsg3-region (apsg3-address-base a4)) 0)
        (<= x 2147483645)
        (apsg3-framed-p)
        (apsg3-linked-p)
        (apsg3-is-sint32-p i)
        (apsg3-is-sint32-p i1)
        (apsg3-is-sint32-p i2)
        (apsg3-is-sint32-p i3)
        (apsg3-valid-rw-p a1 1)
        (apsg3-is-sint32-p x)
        (apsg3-valid-rw-p a7 2147483646)
        (apsg3-separated-p a1 1 a7 2147483646)
        (apsg3-separated-p a6 4 a7 2147483646)
        (apsg3-p-linked-n-p
         :t3 a5-havoc-start a5-havoc-length
         a a4 i2 i1 a3)
        (apsg3-array-swipe-right-p
         a5-havoc-start a5-havoc-length
         a4 x1 (+ 1 i1 i2))
        (apsg3-p-linked-n-p
         :a5 a5-havoc-start a5-havoc-length
         a a4 i2 (- i3 i2) a2)
        (apsg3-p-linked-n-p
         :a5 a5-havoc-start a5-havoc-length
         a2 a4 x1 (- (+ i1 i2) i3) a3)
        (apsg3-unchanged-p
         a5-havoc-start a5-havoc-length a4 i2 i3)
        (apsg3-a1-separated-t3-range-p a1 a4 i2 x)
        (apsg3-t3-range-separated-from-array-p a7 a4 i2 x)
        (apsg3-t3-range-addresses-distinct-p a4 i2 x)
        (apsg3-t3-range-addresses-separated-p a4 i2 x)
        (apsg3-a1-separated-a5-open-closed-range-p
         a1 a4 i3 x a5-havoc-start a5-havoc-length)
        (apsg3-a5-range-separated-from-array-p
         a7 a4 i2 (+ i i1 i2)
         a5-havoc-start a5-havoc-length))
       (apsg3-separated-p
        (apsg3-updated-read
         a8-havoc-start a8-havoc-length
         a8-update-address
         (apsg3-shift a4 i5))
        4
        (apsg3-updated-read
         a8-havoc-start a8-havoc-length
         a8-update-address
         (apsg3-shift a4 i4))
        4))))))

(value-triple :itpeval-statement-checked)

:q
