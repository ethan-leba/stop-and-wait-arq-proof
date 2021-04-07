; ****************** BEGIN INITIALIZATION FOR ACL2s MODE ****************** ;
; (Nothing to see here!  Your actual file is after this initialization code);
(make-event
 (er-progn
  (set-deferred-ttag-notes t state)
  (value '(value-triple :invisible))))

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading the CCG book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/ccg/ccg" :uncertified-okp nil :dir :system :ttags ((:ccg)) :load-compiled-file nil);v4.0 change

;Common base theory for all modes.
#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s base theory book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/base-theory" :dir :system :ttags :all)


#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s customizations book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/custom" :dir :system :ttags :all)

;; guard-checking-on is in *protected-system-state-globals* so any
;; changes are reverted back to what they were if you try setting this
;; with make-event. So, in order to avoid the use of progn! and trust
;; tags (which would not have been a big deal) in custom.lisp, I
;; decided to add this here.
;; 
;; How to check (f-get-global 'guard-checking-on state)
;; (acl2::set-guard-checking :nowarn)
(acl2::set-guard-checking :all)

;Settings common to all ACL2s modes
(acl2s-common-settings)
;(acl2::xdoc acl2s::defunc) ;; 3 seconds is too much time to spare -- commenting out [2015-02-01 Sun]

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s customizations book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/acl2s-sigs" :dir :system :ttags :all)

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem setting up ACL2s mode.") (value :invisible))

(acl2::xdoc acl2s::defunc) ; almost 3 seconds

; Non-events:
;(set-guard-checking :none)

(set-inhibit-warnings! "Invariant-risk" "theory")

(in-package "ACL2")
(redef+)
(defun print-ttag-note (val active-book-name include-bookp deferred-p state)
  (declare (xargs :stobjs state)
	   (ignore val active-book-name include-bookp deferred-p))
  state)

(defun print-deferred-ttag-notes-summary (state)
  (declare (xargs :stobjs state))
  state)

(defun notify-on-defttag (val active-book-name include-bookp state)
  (declare (xargs :stobjs state)
	   (ignore val active-book-name include-bookp))
  state)
(redef-)

(acl2::in-package "ACL2S")

; ******************* END INITIALIZATION FOR ACL2s MODE ******************* ;
;$ACL2s-SMode$;ACL2s

(defmacro let-match* (binds body)
  (case-match binds
    ('() body)
    (((pat val) . rst)
     `(let ((greatbadness ,val))
       (case-match greatbadness
	 (,pat (let-match* ,rst ,body)))))))

;; ---- Definitions ----

(defdata data (listof atom))

(defdata sender-state `(sendstate ,data))

(defdata receiver-state `(recvstate ,data))

(defdata ack nat)

;; Sim-state -- (sender-state receiver-state steps)
(defdata sim-state `(sim-state ,sender-state ,receiver-state ,nat))

;; LHS contains the sender's updated state, RHS is the packet to be sent
(defdata sender-out `(sender-out ,sender-state ,atom))

;; LHS contains the sender's updated state, RHS is the packet to be sent
(defdata receiver-out `(receiver-out ,receiver-state ,ack))

;; ---- Functions ----

(definec sender (sender-state :sender-state) :sender-out
  "This function represents the behavior of the sender in the stop-and-wait ARQ."
  (let-match* ((('sendstate to-send) sender-state))
    `(sender-out (sendstate ,(cdr to-send)) ,(car to-send))))

(set-ignore-ok t)
;; No-op, for now
(definec sender-ack (sender-state :sender-state ack :ack) :sender-state
  sender-state)

(definec receiver (receiver-state :receiver-state packet :atom) :receiver-out
  (let-match* ((('recvstate data) receiver-state))
    `(receiver-out (recvstate ,(app data (list packet))) 0)))

(definec steps-left (sim :sim-state) :bool
  (let-match* ((('sim-state & & steps) sim))
	      (posp steps)))

(definec simulator-step (sim :sim-state) :sim-state
  :ic (steps-left sim)
  (let-match* ((('sim-state ss rs steps) sim)
	       (('sender-out waiting-on-ack-ss packet) (sender ss))
	       (('receiver-out new-rs ack) (receiver rs packet))
	       (new-ss (sender-ack waiting-on-ack-ss ack)))
    `(sim-state ,new-ss ,new-rs ,(1- steps))))

(check= (simulator-step '(sim-state (sendstate (1 2)) (recvstate nil) 3))
	'(sim-state (sendstate (2)) (recvstate (1)) 2))
(check= (simulator-step '(sim-state (sendstate (1)) (recvstate (4 5 6)) 1))
	'(sim-state (sendstate ()) (recvstate (4 5 6 1)) 0))

(definec more-items-than-steps (sim :sim-state) :bool
  (let-match* ((('sim-state ('sendstate ss) & steps) sim))
    (>= (len ss) steps)))

(definec simulator (sim :sim-state) :data
  :ic (more-items-than-steps sim)
  (let-match* ((('sim-state & ('recvstate rs) steps) sim))
	      (cond
	       ((zp steps) rs)
	       (T (simulator (simulator-step sim))))))

(check= (simulator '(sim-state (sendstate (1)) (recvstate (4 5 6)) 0))
	'(4 5 6))

;; ---- Proofs ----

(definec simulator* (data :data steps :nat) :data
  :ic (>= (len data) steps)
  (simulator `(sim-state (sendstate ,data) (recvstate nil) ,steps)))

(definec take2 (data :tl n :nat) :tl
  :ic (>= (len data) n)
  (if (zp n)
      '()
    (cons (car data) (take2 (cdr data) (1- n)))))

;; Checks if x is a prefix of y
(definec prefixp (x :tl y :tl) :bool
  (cond
   ((lendp x) T)
   ((lendp y) (lendp x))
   (T (and (equal (car x) (car y))
	   (prefixp (cdr x) (cdr y))))))

(defthm take2-always-a-prefix
  (implies (and (tlp x)
		(natp n)
		(>= (len x) n))
	   (prefixp (take2 x n) x)))

(defthm take2-sim-relation
  (implies (and (sim-statep sim)
		(more-items-than-steps sim))
	   (equal (simulator sim)
		  (let-match* ((('sim-state ('sendstate ss) ('recvstate rs) steps) sim))
		    (app rs (take2 ss steps))))))

(defthm sim*-equiv-take2
  (implies (and (datap d)
		(natp n)
		(>= (len d) n))
	   (equal (simulator* d n) (take2 d n))))

(defthm data-never-out-of-order
  (implies (and (datap d)
		(natp n)
		(>= (len d) n))
	   (prefixp (simulator* d n) d)))

 
