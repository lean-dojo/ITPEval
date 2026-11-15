;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/contiki_list/linked_n_split_segment_direct_Why3_ide_VClinked_n_split_segment_direct_post_goal0:
;; direct extraction of a prefix of an inductively defined linked-list segment,
;; ending at the pointer stored at index i + i_2. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun lnssdpg0-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun lnssdpg0-address-base (address)
  (car address))

(defun lnssdpg0-address-offset (address)
  (cdr address))

(defun lnssdpg0-shift (address amount)
  (cons
   (lnssdpg0-address-base address)
   (+ (lnssdpg0-address-offset address) amount)))

;; These conservative symbols represent the universally arbitrary source
;; pointer function t_1, integer function t, region operation, and the linked
;; proposition specialized to t.

(defstub lnssdpg0-t1 (address) t)
(defstub lnssdpg0-t (index) t)
(defstub lnssdpg0-region (base) t)
(defstub lnssdpg0-linked-op () t)

(defun-sk lnssdpg0-function-types-p ()
  (forall (address index base)
    (implies
     (and
      (lnssdpg0-address-p address)
      (integerp index)
      (integerp base))
     (and
      (lnssdpg0-address-p (lnssdpg0-t1 address))
      (integerp (lnssdpg0-t index))
      (integerp (lnssdpg0-region base))))))

(defun lnssdpg0-linked-p ()
  (if (lnssdpg0-linked-op) t nil))

(defun lnssdpg0-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun lnssdpg0-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (lnssdpg0-address-base address))
    (<= 0 (lnssdpg0-address-offset address))
    (<=
     (+ (lnssdpg0-address-offset address) length)
     (lnssdpg0-t (lnssdpg0-address-base address))))))

;; This recursion is equivalent to the source inductive p_linked_n relation:
;; n = 0 is exactly its bound constructor, while n > 0 is exactly its cons
;; constructor followed by the unique recursive predecessor at n - 1.

(defun lnssdpg0-p-linked-n-p (root array index n bound)
  (declare (xargs :measure (nfix n)))
  (and
   (lnssdpg0-address-p root)
   (lnssdpg0-address-p array)
   (integerp index)
   (integerp n)
   (lnssdpg0-address-p bound)
   (if (equal n 0)
       (and
        (equal root bound)
        (<= 0 index)
        (<= index 2147483646))
     (and
      (< 0 n)
      (equal
       (lnssdpg0-t1 (lnssdpg0-shift array index))
       root)
      (<= 0 index)
      (<= 0 (+ index n))
      (<= (+ index n) 2147483646)
      (lnssdpg0-valid-rw-p root 4)
      (lnssdpg0-p-linked-n-p
       (lnssdpg0-t1 (lnssdpg0-shift root 0))
       array
       (+ 1 index)
       (- n 1)
       bound)))))

(defun-sk lnssdpg0-framed-p ()
  (forall (address)
    (implies
     (lnssdpg0-address-p address)
     (<=
      (lnssdpg0-region
       (lnssdpg0-address-base (lnssdpg0-t1 address)))
      0))))

(defun-sk
    ntp4vc-linked-n-split-segment-direct-post-goal0-statement ()
  (forall
   (i i2 i1 a a1 a2)
   (implies
    (and
     (lnssdpg0-function-types-p)
     (integerp i)
     (integerp i2)
     (integerp i1)
     (lnssdpg0-address-p a)
     (lnssdpg0-address-p a1)
     (lnssdpg0-address-p a2))
    (let*
        ((a3
          (lnssdpg0-t1
           (lnssdpg0-shift a2 (+ i i2)))))
      (implies
       (and
        (< 0 i)
        (< 0 i1)
        (<= 0 i2)
        (<= (lnssdpg0-region (lnssdpg0-address-base a)) 0)
        (<= (lnssdpg0-region (lnssdpg0-address-base a1)) 0)
        (<= (lnssdpg0-region (lnssdpg0-address-base a2)) 0)
        (<= (lnssdpg0-region (lnssdpg0-address-base a3)) 0)
        (lnssdpg0-framed-p)
        (lnssdpg0-linked-p)
        (lnssdpg0-is-sint32-p i)
        (lnssdpg0-is-sint32-p i1)
        (lnssdpg0-is-sint32-p i2)
        (lnssdpg0-valid-rw-p
         (lnssdpg0-shift a2 0)
         2147483646)
        (lnssdpg0-p-linked-n-p
         a a2 i2 (+ i i1) a1))
       (lnssdpg0-p-linked-n-p
        a a2 i2 i a3))))))

(value-triple :itpeval-statement-checked)

:q
