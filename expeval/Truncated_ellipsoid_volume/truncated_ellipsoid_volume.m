function vol = truncated_ellipsoid_volume(A, k, H)
%TRUNCATED_ELLIPSOID_VOLUME This function computes the volume of a
%truncated ellipsoid. The ellipsoid is given as [x; 1]' * A * [x; 1] < k,
%and the hyperplane is H * [x; 1] < 0.
% tot_vol = compute_volume(A, k)
L=length(H);

[A2, change_basis]= diagonalize_pol_deg_2(A);
H1 = H * change_basis;

new_c = H1(L);
new_h = H1(1:L-1);

vol_const_var = @(c) compute_volume(restric_to_hyperplane(A2, [new_h, -c]), k)/max(abs(new_h));
vol = integral(vol_const_var, -Inf, -new_c, 'ArrayValued', true);
% vol_int_inf = integral(vol_const_var, -Inf, Inf, 'ArrayValued', true)
% fplot(vol_const_var)


end

