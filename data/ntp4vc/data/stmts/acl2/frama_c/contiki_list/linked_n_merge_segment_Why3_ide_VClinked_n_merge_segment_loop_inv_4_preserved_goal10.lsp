;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/contiki_list/linked_n_merge_segment_Why3_ide_VClinked_n_merge_segment_loop_inv_4_preserved_goal10:
;; preservation of an inductively defined linked-list segment invariant while
;; merging adjacent list segments. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun lnmsg10-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun lnmsg10-address-base (address)
  (car address))

(defun lnmsg10-address-offset (address)
  (cdr address))

(defun lnmsg10-shift (address amount)
  (cons
   (lnmsg10-address-base address)
   (+ (lnmsg10-address-offset address) amount)))

;; These conservative symbols represent the universally arbitrary source
;; pointer function t_1, integer function t, region operation, and the linked
;; proposition specialized to t.

(defstub lnmsg10-t1 (address) t)
(defstub lnmsg10-t (index) t)
(defstub lnmsg10-region (base) t)
(defstub lnmsg10-linked-op () t)

(defun-sk lnmsg10-function-types-p ()
  (forall (address index base)
    (implies
     (and
      (lnmsg10-address-p address)
      (integerp index)
      (integerp base))
     (and
      (lnmsg10-address-p (lnmsg10-t1 address))
      (integerp (lnmsg10-t index))
      (integerp (lnmsg10-region base))))))

(defun lnmsg10-linked-p ()
  (if (lnmsg10-linked-op) t nil))

(defun lnmsg10-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun lnmsg10-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (lnmsg10-address-base address))
    (<= 0 (lnmsg10-address-offset address))
    (<=
     (+ (lnmsg10-address-offset address) length)
     (lnmsg10-t (lnmsg10-address-base address))))))

;; This recursion is equivalent to the source inductive p_linked_n relation:
;; n = 0 is exactly its bound constructor, while n > 0 is exactly its cons
;; constructor followed by the unique recursive predecessor at n - 1.

(defun lnmsg10-p-linked-n-p (root array index n bound)
  (declare (xargs :measure (nfix n)))
  (and
   (lnmsg10-address-p root)
   (lnmsg10-address-p array)
   (integerp index)
   (integerp n)
   (lnmsg10-address-p bound)
   (if (equal n 0)
       (and
        (equal root bound)
        (<= 0 index)
        (<= index 2147483646))
     (and
      (< 0 n)
      (equal
       (lnmsg10-t1 (lnmsg10-shift array index))
       root)
      (<= 0 index)
      (<= 0 (+ index n))
      (<= (+ index n) 2147483646)
      (lnmsg10-valid-rw-p root 4)
      (lnmsg10-p-linked-n-p
       (lnmsg10-t1 (lnmsg10-shift root 0))
       array
       (+ 1 index)
       (- n 1)
       bound)))))

(defun-sk lnmsg10-framed-p ()
  (forall (address)
    (implies
     (lnmsg10-address-p address)
     (<=
      (lnmsg10-region
       (lnmsg10-address-base (lnmsg10-t1 address)))
      0))))

(defun-sk
    ntp4vc-linked-n-merge-segment-loop-inv-4-preserved-goal10-statement ()
  (forall
   (i2 i3 a3 i i1 a a1 a2)
   (implies
    (and
     (lnmsg10-function-types-p)
     (integerp i2)
     (integerp i3)
     (lnmsg10-address-p a3)
     (integerp i)
     (integerp i1)
     (lnmsg10-address-p a)
     (lnmsg10-address-p a1)
     (lnmsg10-address-p a2))
    (let*
        ((x (- (+ i2 i3) 1))
         (a4
          (lnmsg10-t1
           (lnmsg10-shift
            (lnmsg10-t1
             (lnmsg10-shift a3 x))
            0))))
      (implies
       (and
        (not (equal i 0))
        (< 0 i3)
        (<= 0 i)
        (<= i3 i)
        (<= 0 i1)
        (<= (lnmsg10-region (lnmsg10-address-base a)) 0)
        (<= (lnmsg10-region (lnmsg10-address-base a1)) 0)
        (<= (lnmsg10-region (lnmsg10-address-base a2)) 0)
        (<= (lnmsg10-region (lnmsg10-address-base a3)) 0)
        (<= 2 i3)
        (lnmsg10-framed-p)
        (lnmsg10-linked-p)
        (lnmsg10-is-sint32-p i)
        (lnmsg10-is-sint32-p i1)
        (lnmsg10-is-sint32-p i2)
        (lnmsg10-is-sint32-p i3)
        (lnmsg10-is-sint32-p (- i3 1))
        (lnmsg10-valid-rw-p
         (lnmsg10-shift a3 0)
         2147483646)
        (lnmsg10-p-linked-n-p
         a a3 i2 i a2)
        (lnmsg10-p-linked-n-p
         a2 a3 (+ i i2) i1 a1)
        (lnmsg10-p-linked-n-p
         a a3 i2 i3 a4)
        (lnmsg10-p-linked-n-p
         a4 a3 (+ i2 i3) (- (+ i i1) i3) a1))
       (lnmsg10-p-linked-n-p
        (lnmsg10-t1
         (lnmsg10-shift
          (lnmsg10-t1
           (lnmsg10-shift a3 (- (+ i2 i3) 2)))
          0))
        a3
        x
        (- (+ 1 i i1) i3)
        a1))))))

(value-triple :itpeval-statement-checked)

:q
