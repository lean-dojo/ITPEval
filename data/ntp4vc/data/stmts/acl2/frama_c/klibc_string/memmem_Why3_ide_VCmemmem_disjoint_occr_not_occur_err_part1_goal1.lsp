;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/klibc_string/memmem_Why3_ide_VCmemmem_disjoint_occr_not_occur_err_part1_goal1:
;; a disjunction of zero-length and size-order cases or the existence of an
;; offset aligning memory reads throughout an integer interval, under the
;; stated linkedness, unsigned bounds, writable-memory, region, and separation
;; hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun mm1-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun mm1-address-base (address)
  (car address))

(defun mm1-address-offset (address)
  (cdr address))

(defun mm1-shift (address amount)
  (cons
   (mm1-address-base address)
   (+ (mm1-address-offset address) amount)))

;; These conservative interfaces represent the universally arbitrary source
;; integer memory t_1, allocation map t, region function, and linked predicate
;; specialized to t.

(defstub mm1-memory (address) t)
(defstub mm1-allocation (index) t)
(defstub mm1-region (base) t)
(defstub mm1-linked-op () t)

(defun-sk mm1-function-types-p ()
  (forall (address index base)
    (and
     (implies
      (mm1-address-p address)
      (integerp (mm1-memory address)))
     (implies
      (integerp index)
      (integerp (mm1-allocation index)))
     (implies
      (integerp base)
      (integerp (mm1-region base))))))

(defun mm1-linked-p ()
  (if (mm1-linked-op) t nil))

(defun mm1-is-uint32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

;; Exact unfoldings of Memory.valid_rw and Memory.separated.

(defun mm1-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (mm1-address-base address))
    (<= 0 (mm1-address-offset address))
    (<=
     (+ (mm1-address-offset address) length)
     (mm1-allocation (mm1-address-base address))))))

(defun mm1-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (mm1-address-base left)
     (mm1-address-base right)))
   (<=
    (+ (mm1-address-offset right) right-length)
    (mm1-address-offset left))
   (<=
    (+ (mm1-address-offset left) left-length)
    (mm1-address-offset right))))

;; The source's inner condition remains universally quantified over every
;; mathematical integer i_3.

(defun-sk mm1-memory-agreement-p (i2 i1 a1 a)
  (forall (i3)
    (implies
     (integerp i3)
     (or
      (equal
       (mm1-memory (mm1-shift a1 (+ i3 i2)))
       (mm1-memory (mm1-shift a i3)))
      (< i3 0)
      (<= i1 i3)))))

;; The offset i_2 remains an internal existential witness.

(defun-sk mm1-offset-exists-p (i i1 a1 a)
  (exists (i2)
    (and
     (integerp i2)
     (<= 0 i2)
     (<= (+ i2 i1) i)
     (mm1-memory-agreement-p i2 i1 a1 a))))

(defun-sk
    ntp4vc-memmem-disjoint-occr-not-occur-err-part1-goal1-statement ()
  (forall
   (a2 a3 i i1 a1 a)
   (implies
    (and
     (mm1-address-p a2)
     (mm1-address-p a3)
     (integerp i)
     (integerp i1)
     (mm1-address-p a1)
     (mm1-address-p a)
     (mm1-function-types-p))
    (let*
        ((a4 (mm1-shift a2 0))
         (a5 (mm1-shift a3 0)))
      (implies
       (and
        (<= 0 i)
        (<= 0 i1)
        (<= (mm1-region (mm1-address-base a2)) 0)
        (<= (mm1-region (mm1-address-base a3)) 0)
        (mm1-linked-p)
        (mm1-is-uint32-p i)
        (mm1-is-uint32-p i1)
        (mm1-valid-rw-p a4 i1)
        (mm1-valid-rw-p a5 i)
        (mm1-separated-p a5 i a4 i1))
       (or
        (equal i 0)
        (equal i1 0)
        (< i i1)
        (and
         (not (equal i 0))
         (not (equal i1 0))
         (<= i1 i))
        (mm1-offset-exists-p i i1 a1 a)))))))

(value-triple :itpeval-statement-checked)

:q
