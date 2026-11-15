;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/verker/strlcpy_Why3_ide_VCstrlcpy_assert_3_goal4:
;; the strlcpy verification condition asserting that the updated destination
;; string has length i_1, under the stated memory, string-validity, unsigned
;; range, allocation, copied-prefix, and non-null-prefix hypotheses. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun sl4-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun sl4-address-base (address)
  (car address))

(defun sl4-address-offset (address)
  (cdr address))

(defun sl4-shift (address amount)
  (cons
   (sl4-address-base address)
   (+ (sl4-address-offset address) amount)))

;; Conservative interfaces represent the universally arbitrary source
;; memories t_1 and t_2, allocation map t, region function, the logical
;; strlen values for t_2 and the updated-memory family, signed and unsigned
;; conversions, and the linked and sconst predicates specialized respectively
;; to t and t_2.

(defstub sl4-t1 (address) t)
(defstub sl4-t2 (address) t)
(defstub sl4-allocation (index) t)
(defstub sl4-region (base) t)
(defstub sl4-l-strlen-t2 (address) t)
(defstub sl4-l-strlen-a4 (a1 i1 address) t)
(defstub sl4-to-uint64 (value) t)
(defstub sl4-to-sint64 (value) t)
(defstub sl4-linked-op () t)
(defstub sl4-sconst-op () t)

;; Preserve the source function types over the full address and unbounded
;; mathematical-integer domains.

(defun-sk sl4-function-types-p ()
  (forall (address index base value a1 i1)
    (and
     (implies
      (sl4-address-p address)
      (and
       (integerp (sl4-t1 address))
       (integerp (sl4-t2 address))
       (integerp (sl4-l-strlen-t2 address))))
     (implies
      (integerp index)
      (integerp (sl4-allocation index)))
     (implies
      (integerp base)
      (integerp (sl4-region base)))
     (implies
      (integerp value)
      (and
       (integerp (sl4-to-uint64 value))
       (integerp (sl4-to-sint64 value))))
     (implies
      (and
       (sl4-address-p a1)
       (integerp i1)
       (sl4-address-p address))
      (integerp
       (sl4-l-strlen-a4 a1 i1 address))))))

(defun sl4-linked-p ()
  (if (sl4-linked-op) t nil))

(defun sl4-sconst-p ()
  (if (sl4-sconst-op) t nil))

;; Exact mathematical ranges for the source C integer predicates.

(defun sl4-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

(defun sl4-is-uint64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

(defun sl4-is-sint64-p (value)
  (and
   (integerp value)
   (<= -9223372036854775808 value)
   (< value 9223372036854775808)))

;; Universal range, identity-on-range, and projection laws for the source's
;; abstract Cint.to_uint64 operation.

(defun-sk sl4-to-uint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (sl4-is-uint64-p
       (sl4-to-uint64 value))
      (implies
       (sl4-is-uint64-p value)
       (equal
        (sl4-to-uint64 value)
        value))
      (equal
       (sl4-to-uint64
        (sl4-to-uint64 value))
       (sl4-to-uint64 value))))))

;; Universal range, identity-on-range, and idempotence laws for the source's
;; abstract Cint.to_sint64 operation.

(defun-sk sl4-to-sint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (sl4-is-sint64-p
       (sl4-to-sint64 value))
      (implies
       (sl4-is-sint64-p value)
       (equal
        (sl4-to-sint64 value)
        value))
      (equal
       (sl4-to-sint64
        (sl4-to-sint64 value))
       (sl4-to-sint64 value))))))

;; Universal source projection equation relating signed and unsigned
;; 64-bit conversions.

(defun-sk sl4-proj-int64-law-p ()
  (forall (value)
    (implies
     (integerp value)
     (equal
      (sl4-to-sint64
       (sl4-to-uint64 value))
      (sl4-to-sint64 value)))))

;; Exact unfoldings of Memory.valid_rd, Memory.valid_rw, and Memory.separated.

(defun sl4-valid-rd-p (address length)
  (implies
   (< 0 length)
   (and
    (not
     (equal 0 (sl4-address-base address)))
    (<= 0 (sl4-address-offset address))
    (<=
     (+ (sl4-address-offset address) length)
     (sl4-allocation
      (sl4-address-base address))))))

(defun sl4-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (sl4-address-base address))
    (<= 0 (sl4-address-offset address))
    (<=
     (+ (sl4-address-offset address) length)
     (sl4-allocation
      (sl4-address-base address))))))

(defun sl4-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (sl4-address-base left)
     (sl4-address-base right)))
   (<=
    (+ (sl4-address-offset right) right-length)
    (sl4-address-offset left))
   (<=
    (+ (sl4-address-offset left) left-length)
    (sl4-address-offset right))))

;; Exact pointwise content of Memory.havoc_access for
;; havoc t_1 t_2 (shift a_1 0) i_1.

(defun sl4-a3-read (address a1 i1)
  (let
      ((a2 (sl4-shift a1 0)))
    (if (sl4-separated-p address 1 a2 i1)
        (sl4-t2 address)
      (sl4-t1 address))))

;; Exact functional update a_3(shift a_1 i_1 := 0), including aliasing.

(defun sl4-a4-read (address a1 i1)
  (if (equal address (sl4-shift a1 i1))
      0
    (sl4-a3-read address a1 i1)))

;; Exact unfolding of A_Strlen.p_valid_str for t_2. The terminating position
;; remains internally existential, and the character condition remains
;; universal over every mathematical integer.

(defun-sk sl4-t2-chars-sint8-through-p
    (address bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= position bound)
      (sl4-is-sint8-p
       (sl4-t2
        (sl4-shift address position)))))))

(defun-sk sl4-t2-valid-string-p (address)
  (exists (index)
    (and
     (integerp index)
     (equal
      (sl4-t2
       (sl4-shift address index))
      0)
     (sl4-is-uint64-p index)
     (sl4-valid-rw-p
      (sl4-shift address 0)
      (+ 1 index))
     (sl4-t2-chars-sint8-through-p
      address index))))

;; Exact unfolding of A_Strlen.p_valid_str for the updated memory a_4.

(defun-sk sl4-a4-chars-sint8-through-p
    (a1 i1 address bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= position bound)
      (sl4-is-sint8-p
       (sl4-a4-read
        (sl4-shift address position)
        a1 i1))))))

(defun-sk sl4-a4-valid-string-p
    (a1 i1 address)
  (exists (index)
    (and
     (integerp index)
     (equal
      (sl4-a4-read
       (sl4-shift address index)
       a1 i1)
      0)
     (sl4-is-uint64-p index)
     (sl4-valid-rw-p
      (sl4-shift address 0)
      (+ 1 index))
     (sl4-a4-chars-sint8-through-p
      a1 i1 address index))))

;; Universal closures of A_Strlen.fix_l_strlen and Q_TL_strlen for t_2 and
;; every updated-memory instance used by the verification condition.

(defun-sk sl4-t2-strlen-laws-p ()
  (forall (address)
    (implies
     (sl4-address-p address)
     (and
      (if
          (equal
           (sl4-t2
            (sl4-shift address 0))
           0)
          (equal
           (sl4-l-strlen-t2 address)
           0)
        (equal
         (sl4-to-uint64
          (+ 1
             (sl4-l-strlen-t2
              (sl4-shift address 1))))
         (sl4-l-strlen-t2 address)))
      (sl4-is-uint64-p
       (sl4-l-strlen-t2 address))))))

(defun-sk sl4-a4-strlen-laws-p ()
  (forall (a1 i1 address)
    (implies
     (and
      (sl4-address-p a1)
      (integerp i1)
      (sl4-address-p address))
     (and
      (if
          (equal
           (sl4-a4-read
            (sl4-shift address 0)
            a1 i1)
           0)
          (equal
           (sl4-l-strlen-a4 a1 i1 address)
           0)
        (equal
         (sl4-to-uint64
          (+ 1
             (sl4-l-strlen-a4
              a1 i1
              (sl4-shift address 1))))
         (sl4-l-strlen-a4 a1 i1 address)))
      (sl4-is-uint64-p
       (sl4-l-strlen-a4 a1 i1 address))))))

;; These extensional predicates preserve that l_strlen is one function of a
;; memory and an address, rather than unrelated symbols for the two memory
;; representations used in this first-order ACL2 encoding.

(defun-sk sl4-a4-equals-t2-p (a1 i1)
  (forall (address)
    (implies
     (sl4-address-p address)
     (equal
      (sl4-a4-read address a1 i1)
      (sl4-t2 address)))))

(defun-sk sl4-a4-instances-equal-p
    (a1 i1 other-a1 other-i1)
  (forall (address)
    (implies
     (sl4-address-p address)
     (equal
      (sl4-a4-read address a1 i1)
      (sl4-a4-read
       address other-a1 other-i1)))))

(defun-sk sl4-strlen-extensionality-p ()
  (forall (a1 i1 other-a1 other-i1 address)
    (implies
     (and
      (sl4-address-p a1)
      (integerp i1)
      (sl4-address-p other-a1)
      (integerp other-i1)
      (sl4-address-p address))
     (and
      (implies
       (sl4-a4-equals-t2-p a1 i1)
       (equal
        (sl4-l-strlen-a4 a1 i1 address)
        (sl4-l-strlen-t2 address)))
      (implies
       (sl4-a4-instances-equal-p
        a1 i1 other-a1 other-i1)
       (equal
        (sl4-l-strlen-a4 a1 i1 address)
        (sl4-l-strlen-a4
         other-a1 other-i1 address)))))))

;; Preserve both internal universal hypotheses over all mathematical integers.

(defun-sk sl4-no-null-before-t2-length-p
    (address length)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= 0 position)
      (implies
       (< position length)
       (not
        (equal
         (sl4-t2
          (sl4-shift address position))
         0)))))))

(defun-sk sl4-a3-prefix-equal-p
    (a1 a i1)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= 0 position)
      (implies
       (< position i1)
       (equal
        (sl4-a3-read
         (sl4-shift a1 position)
         a1 i1)
        (sl4-a3-read
         (sl4-shift a position)
         a1 i1)))))))

(defun-sk
    ntp4vc-strlcpy-assert-3-goal4-statement ()
  (forall
   (a1 a i1 i)
   (implies
    (and
     (sl4-address-p a1)
     (sl4-address-p a)
     (integerp i1)
     (integerp i)
     (sl4-function-types-p)
     (sl4-to-uint64-laws-p)
     (sl4-to-sint64-laws-p)
     (sl4-proj-int64-law-p)
     (sl4-t2-strlen-laws-p)
     (sl4-a4-strlen-laws-p)
     (sl4-strlen-extensionality-p))
    (let*
        ((x
          (sl4-address-base a1))
         (x1
          (sl4-address-base a))
         (x2
          (sl4-l-strlen-t2 a))
         (a2
          (sl4-shift a1 0)))
      (implies
       (and
        (not (equal i 0))
        (not (equal x x1))
        (equal
         (sl4-t2
          (sl4-shift a x2))
         0)
        (<= (sl4-region x1) 0)
        (<= (sl4-region x) 0)
        (sl4-linked-p)
        (sl4-sconst-p)
        (sl4-is-uint64-p i)
        (sl4-is-uint64-p i1)
        (sl4-t2-valid-string-p a)
        (sl4-is-uint64-p x2)
        (sl4-valid-rd-p
         (sl4-shift a 0)
         i1)
        (sl4-valid-rw-p a2 i)
        (sl4-valid-rw-p a2 i1)
        (sl4-a4-valid-string-p
         a1 i1 a1)
        (if (<= i x2)
            (equal
             (sl4-to-uint64 (- i 1))
             i1)
          (equal x2 i1))
        (sl4-no-null-before-t2-length-p
         a x2)
        (sl4-a3-prefix-equal-p
         a1 a i1))
       (equal
        (sl4-l-strlen-a4 a1 i1 a1)
        i1))))))

(value-triple :itpeval-statement-checked)

:q
