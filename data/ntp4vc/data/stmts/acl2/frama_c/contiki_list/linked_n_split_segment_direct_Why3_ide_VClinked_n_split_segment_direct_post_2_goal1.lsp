;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/contiki_list/linked_n_split_segment_direct_Why3_ide_VClinked_n_split_segment_direct_post_2_goal1:
;; direct extraction of the suffix of an inductively defined linked-list
;; segment at the pointer stored at index i + i_2. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun lnssdpg1-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun lnssdpg1-address-base (address)
  (car address))

(defun lnssdpg1-address-offset (address)
  (cdr address))

(defun lnssdpg1-shift (address amount)
  (cons
   (lnssdpg1-address-base address)
   (+ (lnssdpg1-address-offset address) amount)))

;; These conservative symbols represent the universally arbitrary source
;; pointer function t_1, integer function t, region operation, and the linked
;; proposition specialized to t.

(defstub lnssdpg1-t1 (address) t)
(defstub lnssdpg1-t (index) t)
(defstub lnssdpg1-region (base) t)
(defstub lnssdpg1-linked-op () t)

(defun-sk lnssdpg1-function-types-p ()
  (forall (address index base)
    (implies
     (and
      (lnssdpg1-address-p address)
      (integerp index)
      (integerp base))
     (and
      (lnssdpg1-address-p (lnssdpg1-t1 address))
      (integerp (lnssdpg1-t index))
      (integerp (lnssdpg1-region base))))))

(defun lnssdpg1-linked-p ()
  (if (lnssdpg1-linked-op) t nil))

(defun lnssdpg1-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun lnssdpg1-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (lnssdpg1-address-base address))
    (<= 0 (lnssdpg1-address-offset address))
    (<=
     (+ (lnssdpg1-address-offset address) length)
     (lnssdpg1-t (lnssdpg1-address-base address))))))

;; This recursion is equivalent to the source inductive p_linked_n relation:
;; n = 0 is exactly its bound constructor, while n > 0 is exactly its cons
;; constructor followed by the unique recursive predecessor at n - 1.

(defun lnssdpg1-p-linked-n-p (root array index n bound)
  (declare (xargs :measure (nfix n)))
  (and
   (lnssdpg1-address-p root)
   (lnssdpg1-address-p array)
   (integerp index)
   (integerp n)
   (lnssdpg1-address-p bound)
   (if (equal n 0)
       (and
        (equal root bound)
        (<= 0 index)
        (<= index 2147483646))
     (and
      (< 0 n)
      (equal
       (lnssdpg1-t1 (lnssdpg1-shift array index))
       root)
      (<= 0 index)
      (<= 0 (+ index n))
      (<= (+ index n) 2147483646)
      (lnssdpg1-valid-rw-p root 4)
      (lnssdpg1-p-linked-n-p
       (lnssdpg1-t1 (lnssdpg1-shift root 0))
       array
       (+ 1 index)
       (- n 1)
       bound)))))

(defun-sk lnssdpg1-framed-p ()
  (forall (address)
    (implies
     (lnssdpg1-address-p address)
     (<=
      (lnssdpg1-region
       (lnssdpg1-address-base (lnssdpg1-t1 address)))
      0))))

(defun-sk
    ntp4vc-linked-n-split-segment-direct-post-2-goal1-statement ()
  (forall
   (i i2 i1 a a1 a2)
   (implies
    (and
     (lnssdpg1-function-types-p)
     (integerp i)
     (integerp i2)
     (integerp i1)
     (lnssdpg1-address-p a)
     (lnssdpg1-address-p a1)
     (lnssdpg1-address-p a2))
    (let*
        ((x (+ i i2))
         (a3 (lnssdpg1-t1 (lnssdpg1-shift a2 x))))
      (implies
       (and
        (< 0 i)
        (< 0 i1)
        (<= 0 i2)
        (<= (lnssdpg1-region (lnssdpg1-address-base a)) 0)
        (<= (lnssdpg1-region (lnssdpg1-address-base a1)) 0)
        (<= (lnssdpg1-region (lnssdpg1-address-base a2)) 0)
        (<= (lnssdpg1-region (lnssdpg1-address-base a3)) 0)
        (lnssdpg1-framed-p)
        (lnssdpg1-linked-p)
        (lnssdpg1-is-sint32-p i)
        (lnssdpg1-is-sint32-p i1)
        (lnssdpg1-is-sint32-p i2)
        (lnssdpg1-valid-rw-p
         (lnssdpg1-shift a2 0)
         2147483646)
        (lnssdpg1-p-linked-n-p
         a a2 i2 (+ i i1) a1))
       (lnssdpg1-p-linked-n-p
        a3 a2 x i1 a1))))))

(value-triple :itpeval-statement-checked)

:q
