function [M2, change_basis]= diagonalize_pol_deg_2(M)
%DIAGONALIZE_POL_DEG_2 Summary of this function goes here
%   Detailed explanation goes here
N=size(M,1);
A = M(1:N-1,1:N-1);

[Change_basis, ~] = eig(A);
assert(norm(Change_basis*Change_basis' - eye(N-1))/norm(Change_basis) < 1e-5 )

full_change=[Change_basis, zeros(N-1,1); zeros(1,N-1), 1];
M1 = full_change'*M*full_change;

A1 = M1(1:N-1,1:N-1);
b = M1(1:N-1,N);
c = M1(N,N);

P = - A1\b;
Change_basis1=[eye(N-1), P;  zeros(1,N-1), 1];
M2 = Change_basis1'*M1*Change_basis1;
change_basis = full_change * Change_basis1;
end

