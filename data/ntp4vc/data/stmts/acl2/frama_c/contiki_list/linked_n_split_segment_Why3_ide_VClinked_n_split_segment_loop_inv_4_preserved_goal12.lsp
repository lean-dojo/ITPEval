;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/contiki_list/linked_n_split_segment_Why3_ide_VClinked_n_split_segment_loop_inv_4_preserved_goal12:
;; preservation of an inductively defined linked-list suffix invariant while
;; splitting a list segment. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun lnssg12-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun lnssg12-address-base (address)
  (car address))

(defun lnssg12-address-offset (address)
  (cdr address))

(defun lnssg12-shift (address amount)
  (cons
   (lnssg12-address-base address)
   (+ (lnssg12-address-offset address) amount)))

;; These conservative symbols represent the universally arbitrary source
;; pointer function t_1, integer function t, region operation, and the linked
;; proposition specialized to t.

(defstub lnssg12-t1 (address) t)
(defstub lnssg12-t (index) t)
(defstub lnssg12-region (base) t)
(defstub lnssg12-linked-op () t)

(defun-sk lnssg12-function-types-p ()
  (forall (address index base)
    (implies
     (and
      (lnssg12-address-p address)
      (integerp index)
      (integerp base))
     (and
      (lnssg12-address-p (lnssg12-t1 address))
      (integerp (lnssg12-t index))
      (integerp (lnssg12-region base))))))

(defun lnssg12-linked-p ()
  (if (lnssg12-linked-op) t nil))

(defun lnssg12-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun lnssg12-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (lnssg12-address-base address))
    (<= 0 (lnssg12-address-offset address))
    (<=
     (+ (lnssg12-address-offset address) length)
     (lnssg12-t (lnssg12-address-base address))))))

;; This recursion is equivalent to the source inductive p_linked_n relation:
;; n = 0 is exactly its bound constructor, while n > 0 is exactly its cons
;; constructor followed by the unique recursive predecessor at n - 1.

(defun lnssg12-p-linked-n-p (root array index n bound)
  (declare (xargs :measure (nfix n)))
  (and
   (lnssg12-address-p root)
   (lnssg12-address-p array)
   (integerp index)
   (integerp n)
   (lnssg12-address-p bound)
   (if (equal n 0)
       (and
        (equal root bound)
        (<= 0 index)
        (<= index 2147483646))
     (and
      (< 0 n)
      (equal
       (lnssg12-t1 (lnssg12-shift array index))
       root)
      (<= 0 index)
      (<= 0 (+ index n))
      (<= (+ index n) 2147483646)
      (lnssg12-valid-rw-p root 4)
      (lnssg12-p-linked-n-p
       (lnssg12-t1 (lnssg12-shift root 0))
       array
       (+ 1 index)
       (- n 1)
       bound)))))

(defun-sk lnssg12-framed-p ()
  (forall (address)
    (implies
     (lnssg12-address-p address)
     (<=
      (lnssg12-region
       (lnssg12-address-base (lnssg12-t1 address)))
      0))))

(defun-sk
    ntp4vc-linked-n-split-segment-loop-inv-4-preserved-goal12-statement ()
  (forall
   (i1 i3 a2 i i2 a a1)
   (implies
    (and
     (lnssg12-function-types-p)
     (integerp i1)
     (integerp i3)
     (lnssg12-address-p a2)
     (integerp i)
     (integerp i2)
     (lnssg12-address-p a)
     (lnssg12-address-p a1))
    (let*
        ((x (- (+ i1 i3) 1))
         (a3
          (lnssg12-t1
           (lnssg12-shift
            (lnssg12-t1
             (lnssg12-shift a2 x))
            0))))
      (implies
       (and
        (< 0 i)
        (< i i3)
        (<= 0 i1)
        (<= i i2)
        (<= i3 i2)
        (<= i i3)
        (<= (lnssg12-region (lnssg12-address-base a)) 0)
        (<= (lnssg12-region (lnssg12-address-base a1)) 0)
        (<= (lnssg12-region (lnssg12-address-base a2)) 0)
        (<=
         (lnssg12-region
          (lnssg12-address-base
           (lnssg12-t1
            (lnssg12-shift
             (lnssg12-t1
              (lnssg12-shift a2 (- (+ i i1) 1)))
             0))))
         0)
        (lnssg12-framed-p)
        (lnssg12-linked-p)
        (lnssg12-is-sint32-p i)
        (lnssg12-is-sint32-p i1)
        (lnssg12-is-sint32-p i2)
        (lnssg12-is-sint32-p i3)
        (lnssg12-is-sint32-p (- i3 1))
        (lnssg12-is-sint32-p (- i2 i))
        (lnssg12-valid-rw-p
         (lnssg12-shift a2 0)
         2147483646)
        (lnssg12-p-linked-n-p
         a a2 i1 i2 a1)
        (lnssg12-p-linked-n-p
         a a2 i1 i3 a3)
        (lnssg12-p-linked-n-p
         a3 a2 (+ i1 i3) (- i2 i3) a1))
       (lnssg12-p-linked-n-p
        (lnssg12-t1
         (lnssg12-shift
          (lnssg12-t1
           (lnssg12-shift a2 (- (+ i1 i3) 2)))
          0))
        a2
        x
        (- (+ 1 i2) i3)
        a1))))))

(value-triple :itpeval-statement-checked)

:q
