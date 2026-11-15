;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/contiki_list/array_push_Why3_ide_VCarray_push_post_StillLinked_part2_goal10:
;; preservation of the linked-list segment after a null update to a havoced
;; pointer array during array push. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun apg10-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun apg10-address-base (address)
  (car address))

(defun apg10-address-offset (address)
  (cdr address))

(defun apg10-shift (address amount)
  (cons
   (apg10-address-base address)
   (+ (apg10-address-offset address) amount)))

;; These conservative symbols represent the universally arbitrary source
;; functions t_2, t_3, and t, and the fixed region and linked symbols.

(defstub apg10-t2 (address) t)
(defstub apg10-t3 (address) t)
(defstub apg10-malloc (index) t)
(defstub apg10-region (base) t)
(defstub apg10-linked-op () t)

(defun-sk apg10-pointer-functions-p ()
  (forall (address)
    (implies
     (apg10-address-p address)
     (and
      (apg10-address-p (apg10-t2 address))
      (apg10-address-p (apg10-t3 address))))))

(defun-sk apg10-malloc-function-p ()
  (forall (index)
    (implies
     (integerp index)
     (integerp (apg10-malloc index)))))

(defun-sk apg10-region-function-p ()
  (forall (base)
    (implies
     (integerp base)
     (integerp (apg10-region base)))))

(defun apg10-linked-p ()
  (if (apg10-linked-op) t nil))

(defun apg10-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun apg10-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (apg10-address-base left)
     (apg10-address-base right)))
   (<=
    (+ (apg10-address-offset right) right-length)
    (apg10-address-offset left))
   (<=
    (+ (apg10-address-offset left) left-length)
    (apg10-address-offset right))))

(defun apg10-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (apg10-address-base address))
    (<= 0 (apg10-address-offset address))
    (<=
     (+ (apg10-address-offset address) length)
     (apg10-malloc (apg10-address-base address))))))

;; HAVOC-READ is the source memory-theory havoc operation, characterized by
;; its access equation.

(defun apg10-havoc-read
    (havoc-start havoc-length address)
  (if
      (apg10-separated-p address 1 havoc-start havoc-length)
      (apg10-t3 address)
    (apg10-t2 address)))

;; UPDATED-READ is the exact functional update of a havoced memory at the
;; designated array slot with the null address.

(defun apg10-updated-read
    (havoc-start havoc-length update-address address)
  (if (equal address update-address)
      (cons 0 0)
    (apg10-havoc-read havoc-start havoc-length address)))

(defun apg10-mptr-read
    (memory-kind havoc-start havoc-length update-address address)
  (cond
   ((equal memory-kind :t3)
    (apg10-t3 address))
   ((equal memory-kind :a5)
    (apg10-havoc-read havoc-start havoc-length address))
   ((equal memory-kind :updated)
    (apg10-updated-read
     havoc-start havoc-length update-address address))
   (t nil)))

;; This recursion is equivalent to the source inductive p_linked_n relation:
;; n = 0 is its bound constructor, while n > 0 is its cons constructor
;; followed by the unique recursive predecessor at n - 1.

(defun apg10-p-linked-n-p
    (memory-kind havoc-start havoc-length update-address
                 root array index n bound)
  (declare (xargs :measure (nfix n)))
  (and
   (member-eq memory-kind '(:t3 :a5 :updated))
   (apg10-address-p root)
   (apg10-address-p array)
   (integerp index)
   (integerp n)
   (apg10-address-p bound)
   (if (equal n 0)
       (and
        (equal root bound)
        (<= 0 index)
        (<= index 2147483646))
     (and
      (< 0 n)
      (equal
       (apg10-mptr-read
        memory-kind havoc-start havoc-length update-address
        (apg10-shift array index))
       root)
      (<= 0 index)
      (<= 0 (+ index n))
      (<= (+ index n) 2147483646)
      (apg10-valid-rw-p root 4)
      (apg10-p-linked-n-p
       memory-kind havoc-start havoc-length update-address
       (apg10-mptr-read
        memory-kind havoc-start havoc-length update-address
        (apg10-shift root 0))
       array
       (+ 1 index)
       (- n 1)
       bound)))))

(defun-sk apg10-framed-p ()
  (forall (address)
    (implies
     (apg10-address-p address)
     (<=
      (apg10-region
       (apg10-address-base (apg10-t3 address)))
      0))))

(defun-sk apg10-array-swipe-right-p
    (havoc-start havoc-length array down up)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= down index)
      (< index up))
     (equal
      (apg10-t3 (apg10-shift array (- index 1)))
      (apg10-havoc-read
       havoc-start havoc-length
       (apg10-shift array index))))))

;; The source p_unchanged uses the same malloc function and real-valued memory
;; on both sides. Unfolding load_s1_list and eqs1_list makes the real fields
;; equal once the selected addresses are equal; the next-pointer equality and
;; valid_rw implication below are precisely the remaining conjuncts.

(defun-sk apg10-unchanged-p
    (havoc-start havoc-length array down up)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= down index)
      (< index up))
     (let*
         ((slot (apg10-shift array index))
          (left-address
           (apg10-havoc-read
            havoc-start havoc-length slot))
          (right-address (apg10-t3 slot)))
       (and
        (equal left-address right-address)
        (equal
         (apg10-t3 (apg10-shift right-address 0))
         (apg10-havoc-read
          havoc-start havoc-length
          (apg10-shift left-address 0)))
        (implies
         (apg10-valid-rw-p right-address 4)
         (apg10-valid-rw-p left-address 4)))))))

(defun-sk apg10-a1-separated-t3-range-p
    (a1 array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (apg10-separated-p
      a1 1
      (apg10-t3 (apg10-shift array index))
      4))))

(defun-sk apg10-t3-range-separated-from-array-p
    (array-base array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (apg10-separated-p
      (apg10-t3 (apg10-shift array index))
      4 array-base 2147483646))))

(defun-sk apg10-t3-range-addresses-distinct-p
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
       (apg10-t3 (apg10-shift array left-index))
       (apg10-t3 (apg10-shift array right-index)))))))

(defun-sk apg10-t3-range-addresses-separated-p
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
     (apg10-separated-p
      (apg10-t3 (apg10-shift array left-index))
      4
      (apg10-t3 (apg10-shift array right-index))
      4))))

(defun-sk apg10-a1-separated-a5-open-closed-range-p
    (a1 array lower upper havoc-start havoc-length)
  (forall (index)
    (implies
     (and
      (integerp index)
      (< lower index)
      (<= index upper))
     (apg10-separated-p
      a1 1
      (apg10-havoc-read
       havoc-start havoc-length
       (apg10-shift array index))
      4))))

(defun-sk apg10-a5-range-separated-from-array-p
    (array-base array lower upper havoc-start havoc-length)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (apg10-separated-p
      (apg10-havoc-read
       havoc-start havoc-length
       (apg10-shift array index))
      4 array-base 2147483646))))

(defun-sk
    ntp4vc-array-push-post-stilllinked-part2-goal10-statement ()
  (forall
   (i1 i2 a4 a1 i3 i a a3 a2)
   (implies
    (and
     (integerp i1)
     (integerp i2)
     (apg10-address-p a4)
     (apg10-address-p a1)
     (integerp i3)
     (integerp i)
     (apg10-address-p a)
     (apg10-address-p a3)
     (apg10-address-p a2)
     (apg10-pointer-functions-p)
     (apg10-malloc-function-p)
     (apg10-region-function-p))
    (let*
        ((x (+ i1 i2))
         (a5-havoc-start (apg10-shift a4 (+ 1 i2)))
         (a5-havoc-length i1)
         (a6 (apg10-t3 a1))
         (a7 (apg10-shift a4 0))
         (x1 (+ 1 i3))
         (final-havoc-start (apg10-shift a4 x1))
         (final-havoc-length i1)
         (final-update-address (apg10-shift a4 i3)))
      (implies
       (and
        (not (equal i1 0))
        (equal (equal x i3) (equal i 0))
        (equal (< i3 x) (equal i 1))
        (equal
         (apg10-havoc-read
          a5-havoc-start a5-havoc-length a1)
         a6)
        (<= i3 i2)
        (<= i2 i3)
        (<= i3 x)
        (<= (apg10-region (apg10-address-base a)) 0)
        (<= (apg10-region (apg10-address-base a1)) 0)
        (<= (apg10-region (apg10-address-base a3)) 0)
        (<= (apg10-region (apg10-address-base a4)) 0)
        (<= x 2147483645)
        (apg10-framed-p)
        (apg10-linked-p)
        (apg10-is-sint32-p i)
        (apg10-is-sint32-p i1)
        (apg10-is-sint32-p i2)
        (apg10-is-sint32-p i3)
        (apg10-valid-rw-p a1 1)
        (apg10-is-sint32-p x)
        (apg10-valid-rw-p a7 2147483646)
        (apg10-separated-p a1 1 a7 2147483646)
        (apg10-separated-p a6 4 a7 2147483646)
        (apg10-p-linked-n-p
         :t3 a5-havoc-start a5-havoc-length nil
         a a4 i2 i1 a3)
        (apg10-array-swipe-right-p
         a5-havoc-start a5-havoc-length
         a4 x1 (+ 1 i1 i2))
        (apg10-p-linked-n-p
         :a5 a5-havoc-start a5-havoc-length nil
         a a4 i2 (- i3 i2) a2)
        (apg10-p-linked-n-p
         :a5 a5-havoc-start a5-havoc-length nil
         a2 a4 x1 (- (+ i1 i2) i3) a3)
        (apg10-unchanged-p
         a5-havoc-start a5-havoc-length a4 i2 i3)
        (apg10-a1-separated-t3-range-p a1 a4 i2 x)
        (apg10-t3-range-separated-from-array-p a7 a4 i2 x)
        (apg10-t3-range-addresses-distinct-p a4 i2 x)
        (apg10-t3-range-addresses-separated-p a4 i2 x)
        (apg10-a1-separated-a5-open-closed-range-p
         a1 a4 i3 x a5-havoc-start a5-havoc-length)
        (apg10-a5-range-separated-from-array-p
         a7 a4 i2 (+ i i1 i2)
         a5-havoc-start a5-havoc-length))
       (apg10-p-linked-n-p
        :updated final-havoc-start final-havoc-length
        final-update-address
        a a4 x1 i1 a3))))))

(value-triple :itpeval-statement-checked)

:q
