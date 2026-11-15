;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/x509_parser/parse_generalizedTime_Why3_ide_VCparse_generalizedTime_call_compute_decimal_pre_part1_5_goal32:
;; the ASCII decimal-digit lower bound for the byte at generalized-time parser
;; offset fourteen under the VC's address, integer-range, memory-validity,
;; separation, linkedness, and digit-prefix hypotheses. This file contains no
;; proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun gt32-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun gt32-address-base (address)
  (car address))

(defun gt32-address-offset (address)
  (cdr address))

(defun gt32-shift (address amount)
  (cons
   (gt32-address-base address)
   (+ (gt32-address-offset address) amount)))

;; Conservative interfaces represent the universally arbitrary source byte
;; memory t_1 and allocation map t, together with the source region function
;; and the linked proposition specialized to t.

(defstub gt32-byte-memory (address) t)
(defstub gt32-allocation (index) t)
(defstub gt32-region (base) t)
(defstub gt32-linked-op () t)

;; Preserve the source function types over the full address and unbounded
;; mathematical-integer domains.

(defun-sk gt32-function-types-p ()
  (forall (address index base)
    (and
     (implies
      (gt32-address-p address)
      (integerp (gt32-byte-memory address)))
     (implies
      (integerp index)
      (integerp (gt32-allocation index)))
     (implies
      (integerp base)
      (integerp (gt32-region base))))))

(defun gt32-linked-p ()
  (if (gt32-linked-op) t nil))

(defun gt32-is-uint8-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 256)))

(defun gt32-is-uint16-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 65536)))

;; Exact unfoldings of Memory.valid_rw, Memory.valid_rd, and Memory.separated.

(defun gt32-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (gt32-address-base address))
    (<= 0 (gt32-address-offset address))
    (<=
     (+ (gt32-address-offset address) length)
     (gt32-allocation (gt32-address-base address))))))

(defun gt32-valid-rd-p (address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (gt32-address-base address)))
    (<= 0 (gt32-address-offset address))
    (<=
     (+ (gt32-address-offset address) length)
     (gt32-allocation (gt32-address-base address))))))

(defun gt32-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (gt32-address-base left)
     (gt32-address-base right)))
   (<=
    (+ (gt32-address-offset right) right-length)
    (gt32-address-offset left))
   (<=
    (+ (gt32-address-offset left) left-length)
    (gt32-address-offset right))))

;; Preserve the source universal condition over every mathematical integer
;; index i_7 from zero (inclusive) to i_1 (exclusive).

(defun-sk gt32-decimal-prefix-p (a7 i1)
  (forall (i7)
    (implies
     (integerp i7)
     (let
         ((x13
           (gt32-byte-memory
            (gt32-shift a7 (+ 2 i7)))))
       (implies
        (<= 0 i7)
        (implies
         (< i7 i1)
         (and
          (<= 48 x13)
          (<= x13 57))))))))

(defun
    ntp4vc-parse-generalizedtime-call-compute-decimal-pre-part1-5-goal32-statement
    (a7 a1 a a2 a3 a4 a5 a6 i i2 i3 i4 i5 i6 i1)
   (implies
    (and
     (gt32-function-types-p)
     (gt32-address-p a7)
     (gt32-address-p a1)
     (gt32-address-p a)
     (gt32-address-p a2)
     (gt32-address-p a3)
     (gt32-address-p a4)
     (gt32-address-p a5)
     (gt32-address-p a6)
     (integerp i)
     (integerp i2)
     (integerp i3)
     (integerp i4)
     (integerp i5)
     (integerp i6)
     (integerp i1))
    (let*
        ((a8 (gt32-shift a7 0))
         (a9 (gt32-shift a7 1))
         (a10 (gt32-shift a7 16))
         (a11 (gt32-shift a7 2))
         (x (gt32-byte-memory a11))
         (a12 (gt32-shift a7 3))
         (x1 (gt32-byte-memory a12))
         (a13 (gt32-shift a7 4))
         (x2 (gt32-byte-memory a13))
         (a14 (gt32-shift a7 5))
         (x3 (gt32-byte-memory a14))
         (a15 (gt32-shift a7 6))
         (x4 (gt32-byte-memory a15))
         (a16 (gt32-shift a7 7))
         (x5 (gt32-byte-memory a16))
         (a17 (gt32-shift a7 8))
         (x6 (gt32-byte-memory a17))
         (a18 (gt32-shift a7 9))
         (x7 (gt32-byte-memory a18))
         (a19 (gt32-shift a7 10))
         (x8 (gt32-byte-memory a19))
         (a20 (gt32-shift a7 11))
         (x9 (gt32-byte-memory a20))
         (a21 (gt32-shift a7 12))
         (x10 (gt32-byte-memory a21))
         (a22 (gt32-shift a7 13))
         (x11 (gt32-byte-memory a22))
         (a23 (gt32-shift a7 14))
         (x12 (gt32-byte-memory a23))
         (a24 (gt32-shift a7 15)))
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
        (equal (gt32-byte-memory a8) 24)
        (equal (gt32-byte-memory a9) 15)
        (equal (gt32-byte-memory a10) 90)
        (<= 0 i)
        (<= 0 i2)
        (<= 0 i3)
        (<= 0 i4)
        (<= 0 i5)
        (<= 0 i6)
        (<= (gt32-region (gt32-address-base a)) 0)
        (<= (gt32-region (gt32-address-base a1)) 0)
        (<= (gt32-region (gt32-address-base a2)) 0)
        (<= (gt32-region (gt32-address-base a3)) 0)
        (<= (gt32-region (gt32-address-base a4)) 0)
        (<= (gt32-region (gt32-address-base a5)) 0)
        (<= (gt32-region (gt32-address-base a6)) 0)
        (<= (gt32-region (gt32-address-base a7)) 0)
        (<= 14 i1)
        (<= 17 i)
        (<= i3 99)
        (<= i4 99)
        (<= i5 99)
        (<= i6 99)
        (<= i2 9999)
        (<= 48 x)
        (<= 48 x1)
        (<= 48 x2)
        (<= 48 x3)
        (<= 48 x4)
        (<= 48 x5)
        (<= 48 x6)
        (<= 48 x7)
        (<= 48 x8)
        (<= 48 x9)
        (<= 48 x10)
        (<= 48 x11)
        (<= x 57)
        (<= x1 57)
        (<= x2 57)
        (<= x3 57)
        (<= x4 57)
        (<= x5 57)
        (<= x6 57)
        (<= x7 57)
        (<= x8 57)
        (<= x9 57)
        (<= x10 57)
        (<= x11 57)
        (gt32-linked-p)
        (gt32-is-uint8-p i1)
        (gt32-is-uint8-p i3)
        (gt32-is-uint8-p i4)
        (gt32-is-uint8-p i5)
        (gt32-is-uint8-p i6)
        (gt32-is-uint16-p i)
        (gt32-is-uint16-p i2)
        (gt32-valid-rw-p a 1)
        (gt32-valid-rw-p a1 1)
        (gt32-valid-rw-p a2 1)
        (gt32-valid-rw-p a3 1)
        (gt32-valid-rw-p a4 1)
        (gt32-valid-rw-p a5 1)
        (gt32-valid-rw-p a6 1)
        (gt32-is-uint8-p x)
        (gt32-is-uint8-p x1)
        (gt32-is-uint8-p x2)
        (gt32-is-uint8-p x3)
        (gt32-is-uint8-p x4)
        (gt32-is-uint8-p x5)
        (gt32-is-uint8-p x6)
        (gt32-is-uint8-p x7)
        (gt32-is-uint8-p x8)
        (gt32-is-uint8-p x9)
        (gt32-is-uint8-p x10)
        (gt32-is-uint8-p x11)
        (gt32-is-uint8-p x12)
        (gt32-is-uint8-p (gt32-byte-memory a24))
        (gt32-valid-rd-p a8 1)
        (gt32-valid-rd-p a9 1)
        (gt32-valid-rd-p a11 1)
        (gt32-valid-rd-p a12 1)
        (gt32-valid-rd-p a13 1)
        (gt32-valid-rd-p a14 1)
        (gt32-valid-rd-p a15 1)
        (gt32-valid-rd-p a16 1)
        (gt32-valid-rd-p a17 1)
        (gt32-valid-rd-p a18 1)
        (gt32-valid-rd-p a19 1)
        (gt32-valid-rd-p a20 1)
        (gt32-valid-rd-p a21 1)
        (gt32-valid-rd-p a22 1)
        (gt32-valid-rd-p a23 1)
        (gt32-valid-rd-p a24 1)
        (gt32-valid-rd-p a10 1)
        (gt32-separated-p a 1 a8 i)
        (gt32-separated-p a1 1 a8 i)
        (gt32-separated-p a2 1 a8 i)
        (gt32-separated-p a3 1 a8 i)
        (gt32-separated-p a4 1 a8 i)
        (gt32-separated-p a5 1 a8 i)
        (gt32-separated-p a6 1 a8 i)
        (gt32-valid-rd-p
         (gt32-shift a7 (+ 2 i1))
         1)
        (implies
         (< 0 i)
         (gt32-valid-rd-p a8 i))
        (gt32-decimal-prefix-p a7 i1))
       (<= 48 x12)))))

(value-triple :itpeval-statement-checked)

:q
