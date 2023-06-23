function value = lyap1_fun(x , size_string)
load('First_try_piecewise_Lyap_size_' + size_string + '.mat')
%PIECEWISE_LYAP Summary of this function goes here
%   Detailed explanation goes here
augm_x = [x;1];
value = augm_x' * P2b * augm_x;

end

