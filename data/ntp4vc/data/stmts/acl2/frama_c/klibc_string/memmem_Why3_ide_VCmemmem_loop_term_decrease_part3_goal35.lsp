;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/klibc_string/memmem_Why3_ide_VCmemmem_loop_term_decrease_part3_goal35:
;; strict decrease of the memmem loop variant under the stated unsigned
;; bounds, byte reads, memory validity, separation, linkedness, and quantified
;; mismatch conditions. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun mm35-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun mm35-address-base (address)
  (car address))

(defun mm35-address-offset (address)
  (cdr address))

(defun mm35-shift (address amount)
  (cons
   (mm35-address-base address)
   (+ (mm35-address-offset address) amount)))

;; These conservative interfaces represent the universally arbitrary source
;; integer memory t_1, allocation map t, region function, and linked predicate
;; specialized to t.

(defstub mm35-memory (address) t)
(defstub mm35-allocation (index) t)
(defstub mm35-region (base) t)
(defstub mm35-linked-op () t)

(defun-sk mm35-function-types-p ()
  (forall (address index base)
    (and
     (implies
      (mm35-address-p address)
      (integerp (mm35-memory address)))
     (implies
      (integerp index)
      (integerp (mm35-allocation index)))
     (implies
      (integerp base)
      (integerp (mm35-region base))))))

(defun mm35-linked-p ()
  (if (mm35-linked-op) t nil))

;; Cint.to_uint32 is the canonical residue in [0, 2^32), the mathematical
;; unsigned 32-bit conversion on every source integer.

(defun mm35-to-uint32 (value)
  (if (integerp value)
      (mod value 4294967296)
    0))

(defun mm35-is-uint32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun mm35-is-uint8-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 256)))

;; Exact unfoldings of Memory.valid_rw and Memory.separated.

(defun mm35-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (mm35-address-base address))
    (<= 0 (mm35-address-offset address))
    (<=
     (+ (mm35-address-offset address) length)
     (mm35-allocation (mm35-address-base address))))))

(defun mm35-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (mm35-address-base left)
     (mm35-address-base right)))
   (<=
    (+ (mm35-address-offset right) right-length)
    (mm35-address-offset left))
   (<=
    (+ (mm35-address-offset left) left-length)
    (mm35-address-offset right))))

;; The source's first internal existential remains quantified over every
;; mathematical integer i_3.

(defun-sk mm35-prefix-mismatch-exists-p (a5 a4 x7)
  (exists (i3)
    (and
     (integerp i3)
     (not
      (equal
       (mm35-memory (mm35-shift a5 i3))
       (mm35-memory (mm35-shift a4 i3))))
     (<= 0 i3)
     (< i3 x7))))

;; The second internal existential preserves the source's nested implications:
;; existence of i_4 does not assert its two antecedent bounds conjunctively.

(defun-sk mm35-inner-witness-exists-p (a3 a2 i1 i3)
  (exists (i4)
    (and
     (integerp i4)
     (implies
      (<= 0 i4)
      (implies
       (<= (+ 3 i4) i1)
       (not
        (equal
         (mm35-memory
          (mm35-shift a3 (+ 2 i4 i3)))
         (mm35-memory
          (mm35-shift a2 (+ 2 i4))))))))))

;; The surrounding source condition remains universal over all integer i_3.

(defun-sk mm35-loop-condition-p (a3 a2 i1 i2)
  (forall (i3)
    (implies
     (integerp i3)
     (implies
      (<= 0 i3)
      (implies
       (< i3 i2)
       (mm35-inner-witness-exists-p a3 a2 i1 i3))))))

(defun-sk
    ntp4vc-memmem-loop-term-decrease-part3-goal35-statement ()
  (forall
   (a8 a9 a1 a i2 a6 i1 a7 i a5 a4 a3 a2)
   (implies
    (and
     (mm35-address-p a8)
     (mm35-address-p a9)
     (mm35-address-p a1)
     (mm35-address-p a)
     (integerp i2)
     (mm35-address-p a6)
     (integerp i1)
     (mm35-address-p a7)
     (integerp i)
     (mm35-address-p a5)
     (mm35-address-p a4)
     (mm35-address-p a3)
     (mm35-address-p a2)
     (mm35-function-types-p))
    (let*
        ((x (mm35-address-base a8))
         (x1 (mm35-address-base a9))
         (x2 (mm35-memory (mm35-shift a1 0)))
         (x3 (mm35-memory (mm35-shift a i2)))
         (x4 (mm35-memory (mm35-shift a1 1)))
         (x5 (mm35-to-uint32 (+ 1 i2)))
         (x6 (mm35-memory (mm35-shift a x5)))
         (a10 (mm35-shift a8 0))
         (a11 (mm35-shift a9 0))
         (a12 (mm35-shift a6 0))
         (x7 (mm35-to-uint32 (- i1 2)))
         (a13 (mm35-shift a7 0)))
      (implies
       (and
        (not (equal i 0))
        (not (equal i1 0))
        (not (equal i1 1))
        (equal x (mm35-address-base a1))
        (equal x1 (mm35-address-base a))
        (not (equal x2 x3))
        (equal x4 x2)
        (equal x6 x4)
        (<= 0 i)
        (<= i1 i)
        (<= 0 i1)
        (<= 0 i2)
        (<= (mm35-region x) 0)
        (<= (mm35-region x1) 0)
        (<= i2 (mm35-to-uint32 (- i i1)))
        (<= (+ i1 i2) (+ 2 i))
        (mm35-linked-p)
        (mm35-is-uint32-p i)
        (mm35-is-uint32-p i1)
        (mm35-is-uint32-p i2)
        (mm35-is-uint8-p x3)
        (mm35-is-uint8-p x2)
        (mm35-is-uint8-p x4)
        (mm35-valid-rw-p a10 i1)
        (mm35-valid-rw-p a11 i)
        (mm35-separated-p a11 i a10 i1)
        (mm35-valid-rw-p a12 x7)
        (mm35-valid-rw-p a13 x7)
        (mm35-separated-p a13 x7 a12 x7)
        (mm35-is-uint8-p x6)
        (implies
         (< 0 x7)
         (not
          (mm35-prefix-mismatch-exists-p a5 a4 x7)))
        (mm35-loop-condition-p a3 a2 i1 i2))
       (< i2 x5))))))

(value-triple :itpeval-statement-checked)

:q
