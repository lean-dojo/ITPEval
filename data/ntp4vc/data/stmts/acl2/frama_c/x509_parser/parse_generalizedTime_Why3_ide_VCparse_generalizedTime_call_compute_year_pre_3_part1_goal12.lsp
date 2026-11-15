;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/x509_parser/parse_generalizedTime_Why3_ide_VCparse_generalizedTime_call_compute_year_pre_3_part1_goal12:
;; the ASCII decimal-digit lower bound for the byte at generalized-time parser
;; offset four under the VC's address, integer-range, memory-validity,
;; separation, linkedness, and digit-prefix hypotheses. This file contains no
;; proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun gty12-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun gty12-address-base (address)
  (car address))

(defun gty12-address-offset (address)
  (cdr address))

(defun gty12-shift (address amount)
  (cons
   (gty12-address-base address)
   (+ (gty12-address-offset address) amount)))

;; Conservative interfaces represent the universally arbitrary source byte
;; memory t_1 and allocation map t, together with the source region function
;; and the linked proposition specialized to t.

(defstub gty12-byte-memory (address) t)
(defstub gty12-allocation (index) t)
(defstub gty12-region (base) t)
(defstub gty12-linked-op () t)

;; Preserve the source function types over the full address and unbounded
;; mathematical-integer domains.

(defun-sk gty12-function-types-p ()
  (forall (address index base)
    (and
     (implies
      (gty12-address-p address)
      (integerp (gty12-byte-memory address)))
     (implies
      (integerp index)
      (integerp (gty12-allocation index)))
     (implies
      (integerp base)
      (integerp (gty12-region base))))))

(defun gty12-linked-p ()
  (if (gty12-linked-op) t nil))

(defun gty12-is-uint8-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 256)))

(defun gty12-is-uint16-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 65536)))

;; Exact unfoldings of Memory.valid_rw, Memory.valid_rd, and Memory.separated.

(defun gty12-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (gty12-address-base address))
    (<= 0 (gty12-address-offset address))
    (<=
     (+ (gty12-address-offset address) length)
     (gty12-allocation (gty12-address-base address))))))

(defun gty12-valid-rd-p (address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (gty12-address-base address)))
    (<= 0 (gty12-address-offset address))
    (<=
     (+ (gty12-address-offset address) length)
     (gty12-allocation (gty12-address-base address))))))

(defun gty12-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (gty12-address-base left)
     (gty12-address-base right)))
   (<=
    (+ (gty12-address-offset right) right-length)
    (gty12-address-offset left))
   (<=
    (+ (gty12-address-offset left) left-length)
    (gty12-address-offset right))))

;; Preserve the source universal condition over every mathematical integer
;; index i_2 from zero (inclusive) to i_1 (exclusive).

(defun-sk gty12-decimal-prefix-p (a7 i1)
  (forall (i2)
    (implies
     (integerp i2)
     (let
         ((x1
           (gty12-byte-memory
            (gty12-shift a7 (+ 2 i2)))))
       (implies
        (<= 0 i2)
        (implies
         (< i2 i1)
         (and
          (<= 48 x1)
          (<= x1 57))))))))

(defun-sk
    ntp4vc-parse-generalizedtime-call-compute-year-pre-3-part1-goal12-statement
    ()
  (forall
   (a7 a1 a a2 a3 a4 a5 a6 i i1)
   (implies
    (and
     (gty12-function-types-p)
     (gty12-address-p a7)
     (gty12-address-p a1)
     (gty12-address-p a)
     (gty12-address-p a2)
     (gty12-address-p a3)
     (gty12-address-p a4)
     (gty12-address-p a5)
     (gty12-address-p a6)
     (integerp i)
     (integerp i1))
    (let*
        ((a8 (gty12-shift a7 0))
         (a9 (gty12-shift a7 1))
         (a10 (gty12-shift a7 16))
         (a11 (gty12-shift a7 2))
         (a12 (gty12-shift a7 3))
         (a13 (gty12-shift a7 4))
         (x (gty12-byte-memory a13))
         (a14 (gty12-shift a7 5)))
      (implies
       (and
        (not (equal a1 a))
        (not (equal a2 a))
        (not (equal a2 a1))
        (not (equal a3 a))
        (not (equal a3 a1))
        (not (equal a3 a2))
        (not (equal a4 a))
        (not (equal a4 a1))
        (not (equal a4 a2))
        (not (equal a4 a3))
        (not (equal a5 a))
        (not (equal a5 a1))
        (not (equal a5 a2))
        (not (equal a5 a3))
        (not (equal a5 a4))
        (not (equal a6 a))
        (not (equal a6 a1))
        (not (equal a6 a2))
        (not (equal a6 a3))
        (not (equal a6 a4))
        (not (equal a6 a5))
        (not (equal (cons 0 0) a7))
        (equal (gty12-byte-memory a8) 24)
        (equal (gty12-byte-memory a9) 15)
        (equal (gty12-byte-memory a10) 90)
        (<= 0 i)
        (<= (gty12-region (gty12-address-base a)) 0)
        (<= (gty12-region (gty12-address-base a1)) 0)
        (<= (gty12-region (gty12-address-base a2)) 0)
        (<= (gty12-region (gty12-address-base a3)) 0)
        (<= (gty12-region (gty12-address-base a4)) 0)
        (<= (gty12-region (gty12-address-base a5)) 0)
        (<= (gty12-region (gty12-address-base a6)) 0)
        (<= (gty12-region (gty12-address-base a7)) 0)
        (<= 14 i1)
        (<= 17 i)
        (gty12-linked-p)
        (gty12-is-uint8-p i1)
        (gty12-is-uint16-p i)
        (gty12-valid-rw-p a 1)
        (gty12-valid-rw-p a1 1)
        (gty12-valid-rw-p a2 1)
        (gty12-valid-rw-p a3 1)
        (gty12-valid-rw-p a4 1)
        (gty12-valid-rw-p a5 1)
        (gty12-valid-rw-p a6 1)
        (gty12-is-uint8-p (gty12-byte-memory a11))
        (gty12-is-uint8-p (gty12-byte-memory a12))
        (gty12-is-uint8-p x)
        (gty12-is-uint8-p (gty12-byte-memory a14))
        (gty12-valid-rd-p a8 1)
        (gty12-valid-rd-p a9 1)
        (gty12-valid-rd-p a11 1)
        (gty12-valid-rd-p a12 1)
        (gty12-valid-rd-p a13 1)
        (gty12-valid-rd-p a14 1)
        (gty12-valid-rd-p a10 1)
        (gty12-separated-p a 1 a8 i)
        (gty12-separated-p a1 1 a8 i)
        (gty12-separated-p a2 1 a8 i)
        (gty12-separated-p a3 1 a8 i)
        (gty12-separated-p a4 1 a8 i)
        (gty12-separated-p a5 1 a8 i)
        (gty12-separated-p a6 1 a8 i)
        (gty12-valid-rd-p
         (gty12-shift a7 (+ 2 i1))
         1)
        (implies
         (< 0 i)
         (gty12-valid-rd-p a8 i))
        (gty12-decimal-prefix-p a7 i1))
       (<= 48 x))))))

(value-triple :itpeval-statement-checked)

:q
