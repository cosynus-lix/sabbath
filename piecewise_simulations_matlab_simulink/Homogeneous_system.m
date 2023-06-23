size_system = 18;
to_Ludo_reformulator

size_string = convertCharsToStrings(num2str(size_system));

load("First_try_piecewise_Lyap_size_" + size_string + ".mat")

printing = 1;
plotting = 1;

% % This is to select a point where P1b is increasing
% der_wrong= A_1_homo_complete' * P1b + P1b * A_1_homo_complete;
% [asdasd, asdasdasd] = eig(der_wrong);
% [~,h] = max(diag(asdasdasd));
% lol = asdasd(:, h);
% lolo = lol / lol(end);
% if invar_mode0_ge * lolo > 0
%     warning = "We are not sure we will get an increading point, since" + ...
%         "we are in mode 0."
% end

% This is a random vector
lolo = 1000*rand(size_system + 4, 1);
lolo = lolo / lolo(end);

[t,y] = ode89(@(t,y) differential_homo_complete(t,y,size_string) , [0 1], lolo);

datahomo=y(:,1:end-1);
last_moment = size(datahomo,1);

lyap_0_fun = @(x) lyap0_fun(x', size_string);
val_lyap_0 = zeros(1, last_moment);
for l = 1 : last_moment
    val_lyap_0(l) = lyap_0_fun(datahomo(l,:));
end
if plotting ==1
    figure
    plot(val_lyap_0)
    hold on
end
if printing ==1
    issorted(-val_lyap_0)
end


lyap_1_fun = @(x) lyap1_fun(x', size_string);
val_lyap_1 = zeros(1, last_moment);
for l = 1 : last_moment
    val_lyap_1(l) = lyap_1_fun(datahomo(l,:));
end
if plotting ==1
    semilogy(val_lyap_1)
end
if printing ==1
    issorted(-val_lyap_1)
end

pc_lyap = @(x) piecewise_lyap(x', size_string);
val_lyap_pc = zeros(1, last_moment);
for l = 1 : last_moment
    val_lyap_pc(l) = pc_lyap(datahomo(l,:));
end

if plotting ==1
    semilogy(val_lyap_pc, 'o')
end

if printing == 1
    lyap_pc_decreasing_check = issorted(-val_lyap_pc)
else
    lyap_pc_decreasing_check = issorted(-val_lyap_pc);
end

diff_Val = zeros (1, length(val_lyap_0)-1);
for indexhere = 1:length(val_lyap_0)-1
    diff_Val(indexhere) = val_lyap_0(indexhere) - val_lyap_0(indexhere + 1);
end
[ll_lyap0, lll_lyap0] = min(diff_Val);


diff_Val = zeros (1, length(val_lyap_1)-1);
for indexhere = 1:length(val_lyap_1)-1
    diff_Val(indexhere) = val_lyap_1(indexhere) - val_lyap_1(indexhere + 1);
end
[ll_lyap1, lll_lyap1] = min(diff_Val);


diff_Val = zeros (1, length(val_lyap_pc)-1);
for indexhere = 1:length(val_lyap_pc)-1
    diff_Val(indexhere) = val_lyap_pc(indexhere) - val_lyap_pc(indexhere + 1);
end
[ll_lyap_pc, lll_lyap_pc] = min(diff_Val);