;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/contiki_list/linked_n_merge_segment_Why3_ide_VClinked_n_merge_segment_loop_inv_3_established_goal9:
;; establishment of the linked-list segment endpoint invariant while merging
;; two adjacent segments. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun lnmsg9-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun lnmsg9-address-base (address)
  (car address))

(defun lnmsg9-address-offset (address)
  (cdr address))

(defun lnmsg9-shift (address amount)
  (cons
   (lnmsg9-address-base address)
   (+ (lnmsg9-address-offset address) amount)))

;; These conservative symbols represent the universally arbitrary source
;; pointer function t_1, integer function t, region operation, and the linked
;; proposition specialized to t.

(defstub lnmsg9-t1 (address) t)
(defstub lnmsg9-t (index) t)
(defstub lnmsg9-region (base) t)
(defstub lnmsg9-linked-op () t)

(defun-sk lnmsg9-function-types-p ()
  (forall (address index base)
    (implies
     (and
      (lnmsg9-address-p address)
      (integerp index)
      (integerp base))
     (and
      (lnmsg9-address-p (lnmsg9-t1 address))
      (integerp (lnmsg9-t index))
      (integerp (lnmsg9-region base))))))

(defun lnmsg9-linked-p ()
  (if (lnmsg9-linked-op) t nil))

(defun lnmsg9-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun lnmsg9-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (lnmsg9-address-base address))
    (<= 0 (lnmsg9-address-offset address))
    (<=
     (+ (lnmsg9-address-offset address) length)
     (lnmsg9-t (lnmsg9-address-base address))))))

;; This recursion is equivalent to the source inductive p_linked_n relation:
;; n = 0 is exactly its bound constructor, while n > 0 is exactly its cons
;; constructor followed by the unique recursive predecessor at n - 1.

(defun lnmsg9-p-linked-n-p (root array index n bound)
  (declare (xargs :measure (nfix n)))
  (and
   (lnmsg9-address-p root)
   (lnmsg9-address-p array)
   (integerp index)
   (integerp n)
   (lnmsg9-address-p bound)
   (if (equal n 0)
       (and
        (equal root bound)
        (<= 0 index)
        (<= index 2147483646))
     (and
      (< 0 n)
      (equal
       (lnmsg9-t1 (lnmsg9-shift array index))
       root)
      (<= 0 index)
      (<= 0 (+ index n))
      (<= (+ index n) 2147483646)
      (lnmsg9-valid-rw-p root 4)
      (lnmsg9-p-linked-n-p
       (lnmsg9-t1 (lnmsg9-shift root 0))
       array
       (+ 1 index)
       (- n 1)
       bound)))))

(defun-sk lnmsg9-framed-p ()
  (forall (address)
    (implies
     (lnmsg9-address-p address)
     (<=
      (lnmsg9-region
       (lnmsg9-address-base (lnmsg9-t1 address)))
      0))))

(defun-sk
    ntp4vc-linked-n-merge-segment-loop-inv-3-established-goal9-statement ()
  (forall
   (i2 i a a1 a2 a3 i1)
   (implies
    (and
     (lnmsg9-function-types-p)
     (integerp i2)
     (integerp i)
     (lnmsg9-address-p a)
     (lnmsg9-address-p a1)
     (lnmsg9-address-p a2)
     (lnmsg9-address-p a3)
     (integerp i1))
    (implies
     (and
      (not (equal i2 0))
      (<= 0 i)
      (<= 0 i2)
      (<= (lnmsg9-region (lnmsg9-address-base a)) 0)
      (<= (lnmsg9-region (lnmsg9-address-base a1)) 0)
      (<= (lnmsg9-region (lnmsg9-address-base a2)) 0)
      (<= (lnmsg9-region (lnmsg9-address-base a3)) 0)
      (lnmsg9-framed-p)
      (lnmsg9-linked-p)
      (lnmsg9-is-sint32-p i)
      (lnmsg9-is-sint32-p i1)
      (lnmsg9-is-sint32-p i2)
      (lnmsg9-valid-rw-p
       (lnmsg9-shift a3 0)
       2147483646)
      (lnmsg9-p-linked-n-p
       a a3 i1 i2 a2)
      (lnmsg9-p-linked-n-p
       a2 a3 (+ i1 i2) i a1))
     (lnmsg9-p-linked-n-p
      a
      a3
      i1
      i2
      (lnmsg9-t1
       (lnmsg9-shift
        (lnmsg9-t1
         (lnmsg9-shift a3 (- (+ i1 i2) 1)))
        0)))))))

(value-triple :itpeval-statement-checked)

:q
