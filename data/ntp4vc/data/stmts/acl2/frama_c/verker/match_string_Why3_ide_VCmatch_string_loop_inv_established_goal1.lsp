;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/verker/match_string_Why3_ide_VCmatch_string_loop_inv_established_goal1:
;; establishment of the match-string loop invariant that the logical real
;; length lies between zero and the supplied unsigned bound. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun mslieg1-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun mslieg1-address-base (address)
  (car address))

(defun mslieg1-address-offset (address)
  (cdr address))

(defun mslieg1-shift (address amount)
  (cons
   (mslieg1-address-base address)
   (+ (mslieg1-address-offset address) amount)))

(defun mslieg1-null-address ()
  (cons 0 0))

;; Conservative interfaces represent the universally arbitrary pointer
;; memory t_2, allocation map t, character memory t_1, region function, and
;; the source logical real-length and unsigned-conversion operations.

(defstub mslieg1-pointer-memory (address) t)
(defstub mslieg1-allocation (index) t)
(defstub mslieg1-character-memory (address) t)
(defstub mslieg1-region (base) t)
(defstub mslieg1-l-real-len (address count) t)
(defstub mslieg1-to-uint64 (value) t)
(defstub mslieg1-linked-op () t)
(defstub mslieg1-sconst-op () t)

;; Preserve the source function types over the full address and unbounded
;; integer domains.

(defun-sk mslieg1-function-types-p ()
  (forall (address index base count)
    (and
     (implies
      (mslieg1-address-p address)
      (and
       (mslieg1-address-p
        (mslieg1-pointer-memory address))
       (integerp
        (mslieg1-character-memory address))))
     (implies
      (integerp index)
      (integerp
       (mslieg1-allocation index)))
     (implies
      (integerp base)
      (integerp
       (mslieg1-region base)))
     (implies
      (and
       (mslieg1-address-p address)
       (integerp count))
      (integerp
       (mslieg1-l-real-len address count))))))

(defun mslieg1-linked-p ()
  (if (mslieg1-linked-op) t nil))

(defun mslieg1-sconst-p ()
  (if (mslieg1-sconst-op) t nil))

;; Exact mathematical ranges for the source C integer predicates.

(defun mslieg1-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

(defun mslieg1-is-uint64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

;; Universal range, identity-on-range, and projection laws for the source's
;; abstract Cint.to_uint64 operation.

(defun-sk mslieg1-to-uint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (mslieg1-is-uint64-p
       (mslieg1-to-uint64 value))
      (implies
       (mslieg1-is-uint64-p value)
       (equal
        (mslieg1-to-uint64 value)
        value))
      (equal
       (mslieg1-to-uint64
        (mslieg1-to-uint64 value))
       (mslieg1-to-uint64 value))))))

;; Exact unfolding of Memory.valid_rw for the fixed allocation map t.

(defun mslieg1-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (mslieg1-address-base address))
    (<= 0 (mslieg1-address-offset address))
    (<=
     (+ (mslieg1-address-offset address) length)
     (mslieg1-allocation
      (mslieg1-address-base address))))))

;; Exact unfolding of Memory.framed for the pointer memory t_2.

(defun-sk mslieg1-framed-p ()
  (forall (address)
    (implies
     (mslieg1-address-p address)
     (<=
      (mslieg1-region
       (mslieg1-address-base
        (mslieg1-pointer-memory address)))
      0))))

;; Exact unfolding of A_Strlen.p_valid_str. Its terminating index remains an
;; internal existential over all mathematical integers.

(defun-sk mslieg1-string-chars-sint8-through-p
    (address bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= position bound)
      (mslieg1-is-sint8-p
       (mslieg1-character-memory
        (mslieg1-shift address position)))))))

(defun-sk mslieg1-valid-string-p (address)
  (exists (index)
    (and
     (integerp index)
     (equal
      (mslieg1-character-memory
       (mslieg1-shift address index))
      0)
     (mslieg1-is-uint64-p index)
     (mslieg1-valid-rw-p
      (mslieg1-shift address 0)
      (+ 1 index))
     (mslieg1-string-chars-sint8-through-p
      address index))))

;; Universal closures of A_MatchString.fix_l_real_len and Q_TL_real_len for
;; the arbitrary pointer memory t_2.

(defun-sk mslieg1-real-len-laws-p ()
  (forall (address count)
    (implies
     (and
      (mslieg1-address-p address)
      (integerp count))
     (and
      (if
          (or
           (equal count 0)
           (equal
            (mslieg1-pointer-memory
             (mslieg1-shift address 0))
            (mslieg1-null-address)))
          (equal
           (mslieg1-l-real-len address count)
           0)
        (equal
         (mslieg1-to-uint64
          (+ 1
             (mslieg1-l-real-len
              (mslieg1-shift address 1)
              (mslieg1-to-uint64
               (- count 1)))))
         (mslieg1-l-real-len address count)))
      (mslieg1-is-uint64-p
       (mslieg1-l-real-len address count))))))

;; The loop hypothesis retains its internal universal quantifier and its
;; original chain of integer, order, unsigned-range, and string-validity
;; conditions.

(defun-sk mslieg1-real-prefix-strings-valid-p
    (a1 bound)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (<= 0 index)
      (implies
       (< index bound)
       (implies
        (mslieg1-is-uint64-p index)
        (mslieg1-valid-string-p
         (mslieg1-pointer-memory
          (mslieg1-shift a1 index)))))))))

(defun-sk
    ntp4vc-match-string-loop-inv-established-goal1-statement ()
  (forall
   (a1 i a)
   (implies
    (and
     (mslieg1-address-p a1)
     (integerp i)
     (mslieg1-address-p a)
     (mslieg1-function-types-p)
     (mslieg1-to-uint64-laws-p)
     (mslieg1-real-len-laws-p))
    (let*
        ((x
          (mslieg1-l-real-len a1 i))
         (a2
          (mslieg1-shift a1 0)))
      (implies
       (and
        (<=
         (mslieg1-region
          (mslieg1-address-base a))
         0)
        (<=
         (mslieg1-region
          (mslieg1-address-base a1))
         0)
        (<= i 2147483647)
        (mslieg1-framed-p)
        (mslieg1-linked-p)
        (mslieg1-sconst-p)
        (mslieg1-is-uint64-p i)
        (mslieg1-valid-string-p a)
        (implies
         (equal x i)
         (mslieg1-valid-rw-p a2 i))
        (implies
         (< x i)
         (mslieg1-valid-rw-p a2 (+ 1 x)))
        (mslieg1-real-prefix-strings-valid-p
         a1 x))
       (and
        (<= x i)
        (<= 0 x)))))))

(value-triple :itpeval-statement-checked)

:q
